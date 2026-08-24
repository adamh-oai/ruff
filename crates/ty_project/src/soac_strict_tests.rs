//! Strict lint tests use real ty project inference, not rendered diagnostic matching.

use super::soac_export_tests::{database, database_with_options};
use ruff_db::files::system_path_to_file;
use soac_contracts::*;
use ty_python_core::AnalysisDialect;
use ty_python_semantic::export_soac_module_facts;

fn analyze(source: &str, policy: ResolvedStrictPolicy) -> ModuleTypeFacts {
    let db = database(source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    export_soac_module_facts(&db, file, "main", policy).unwrap()
}

fn codes(facts: &ModuleTypeFacts) -> Vec<DiagnosticCode> {
    facts
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code != DiagnosticCode::CheckerError)
        .map(|diagnostic| diagnostic.code)
        .collect()
}

#[test]
fn soac_strict_framework_attribute_fallback_preserves_original_metaclass_source() {
    let source = "from __future__ import strict\ndef decorate(cls):\n    cls.decorated = cls.flag + 1\n    return cls\nclass Meta(type):\n    def __new__(mcls, name, bases, ns, **kw):\n        cls = type.__new__(mcls, name, bases, ns)\n        cls.flag = kw['flag']\n        return cls\n@decorate\nclass C(metaclass=Meta, flag=41):\n    pass\nRESULT = C.decorated\n";
    let db = database(source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let checker = ty_python_semantic::Db::check_file(&db, file);
    let unresolved: Vec<_> = checker
        .iter()
        .filter(|diagnostic| diagnostic.id().is_lint_named("unresolved-attribute"))
        .collect();
    assert_eq!(unresolved.len(), 2);
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    for name in ["Meta", "C"] {
        assert!(facts.classes.iter().any(|class| {
            class.identity.lexical_qualname == name
                && matches!(class.participation, ParticipationProposal::Dynamic(_))
        }));
    }
    for diagnostic in unresolved {
        let range = diagnostic.primary_span().unwrap().range().unwrap();
        let range = SourceRange::new(range.start().to_u32(), range.end().to_u32());
        assert!(
            facts.diagnostics.iter().any(|diagnostic| {
                diagnostic.source_range == range
                    && diagnostic.code == DiagnosticCode::StrictUncheckedDynamicType
                    && diagnostic.severity == DiagnosticSeverity::Warning
                    && !diagnostic.suppressed
                    && !diagnostic.related_definitions.is_empty()
            }),
            "missing visible framework fallback at {range:?}"
        );
        let site = facts
            .attribute_sites
            .iter()
            .find(|site| site.identity.expression_range == range)
            .unwrap();
        assert!(site.uncertainty.contains(&UncertaintyReason::Unknown));
        assert!(
            site.value_type
                .as_ref()
                .is_none_or(|ty| *ty == StaticType::Unknown)
        );
    }
    assert!(!facts.diagnostics.iter().any(|diagnostic| {
        diagnostic.severity == DiagnosticSeverity::Error && !diagnostic.suppressed
    }));
    // The SOAC consumer does not alter ordinary ty's cached checking result.
    assert_eq!(
        ty_python_semantic::Db::check_file(&db, file)
            .iter()
            .filter(|diagnostic| diagnostic.id().is_lint_named("unresolved-attribute"))
            .count(),
        2
    );
}

#[test]
fn soac_strict_framework_attribute_fallback_demotes_consuming_calls_and_attributes() {
    let source = "from __future__ import strict\ndef decorate(cls): return cls\n@decorate\nclass Framework: pass\nclass Child(Framework): pass\ndef consume(value: int) -> int: return value\nINSTANCE = Child()\nRESULT = INSTANCE.missing()\nOTHER = consume(INSTANCE.payload)\nTYPE = INSTANCE.payload.__class__\n";
    let facts = analyze(source, ResolvedStrictPolicy::default());
    let child = facts
        .classes
        .iter()
        .find(|class| class.identity.lexical_qualname == "Child")
        .unwrap();
    assert!(matches!(
        child.participation,
        ParticipationProposal::Dynamic(_)
    ));
    let warnings: Vec<_> = facts
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.code == DiagnosticCode::StrictUncheckedDynamicType && !diagnostic.suppressed
        })
        .collect();
    assert_eq!(warnings.len(), 3);
    for warning in warnings {
        assert_eq!(warning.severity, DiagnosticSeverity::Warning);
        assert_eq!(warning.related_definitions, vec![child.identity.clone()]);
        for attribute in facts.attribute_sites.iter().filter(|attribute| {
            attribute.identity.expression_range.start <= warning.source_range.start
                && warning.source_range.end <= attribute.identity.expression_range.end
        }) {
            assert_eq!(attribute.receiver_type, StaticType::Unknown);
            assert_eq!(attribute.value_type, Some(StaticType::Unknown));
            assert!(
                attribute
                    .uncertainty
                    .contains(&UncertaintyReason::DynamicDecorator)
            );
        }
    }
    let affected: Vec<_> = facts
        .call_sites
        .iter()
        .filter(|call| {
            source[call.identity.expression_range.start as usize
                ..call.identity.expression_range.end as usize]
                .contains("INSTANCE.")
        })
        .collect();
    assert_eq!(affected.len(), 2);
    for call in affected {
        assert_eq!(call.binding, CallBindingFact::Dynamic);
        assert_eq!(call.candidate_targets, vec![CallableTargetFact::Dynamic]);
        assert_eq!(call.result_type, StaticType::Unknown);
        assert_eq!(call.uncertainty, CallUncertainty::Dynamic);
        assert!(call.signature.parameters.is_empty());
        assert_eq!(call.signature.return_type, StaticType::Unknown);
    }
    let consume = facts
        .functions
        .iter()
        .find(|function| function.identity.lexical_qualname == "consume")
        .unwrap();
    assert_eq!(consume.signature.parameters.len(), 1);
    assert_eq!(
        consume.signature.parameters[0].annotation_origin,
        AnnotationOrigin::Explicit
    );
    assert!(!facts.diagnostics.iter().any(|diagnostic| {
        diagnostic.severity == DiagnosticSeverity::Error && !diagnostic.suppressed
    }));
}

#[test]
fn soac_strict_framework_attribute_fallback_preserves_real_errors() {
    let source = "from __future__ import strict\nfrom typing import final\nclass Candidate:\n    value: int = 0\nclass Meta(type): pass\nclass Dynamic(metaclass=Meta):\n    value: int = 0\n    def invalid(self, other: Candidate):\n        other.missing\n        self.value = 'wrong'\n        return missing_name\nclass NotAFramework(list[int]):\n    def invalid(self): return self.missing\n@final\nclass Final: pass\nclass BadFinal(Final, metaclass=Meta): pass\nclass Base:\n    @final\n    def method(self, value: int) -> int: return value\nclass BadOverride(Base):\n    def method(self, value: str) -> str: return value\nLIMIT = 1\ndef invalid_global(): globals()['LIMIT'] = 2\n";
    let db = database(source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let checker = ty_python_semantic::Db::check_file(&db, file);
    let errors: Vec<_> = checker
        .iter()
        .filter(|diagnostic| diagnostic.severity() == ruff_db::diagnostic::Severity::Error)
        .collect();
    assert!(errors.len() >= 5);
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    for error in errors {
        let range = error.primary_span().unwrap().range().unwrap();
        let range = SourceRange::new(range.start().to_u32(), range.end().to_u32());
        assert!(
            facts.diagnostics.iter().any(|diagnostic| {
                diagnostic.source_range == range
                    && diagnostic.code == DiagnosticCode::CheckerError
                    && diagnostic.severity == DiagnosticSeverity::Error
                    && !diagnostic.suppressed
            }),
            "lost real checker error {} at {range:?}",
            error.id()
        );
    }
    let codes = codes(&facts);
    assert!(!codes.contains(&DiagnosticCode::StrictUncheckedDynamicType));
    assert!(codes.contains(&DiagnosticCode::StrictFinalClassSubclass));
    assert!(codes.contains(&DiagnosticCode::StrictFinalMethodOverride));
    assert!(codes.contains(&DiagnosticCode::StrictIncompatibleOverride));
    assert!(codes.contains(&DiagnosticCode::StrictFinalGlobalRebind));
}

#[test]
fn soac_strict_framework_attribute_fallback_is_not_ordinary_ty_policy() {
    let ordinary =
        "def decorate(cls): return cls\n@decorate\nclass Dynamic: pass\nRESULT = Dynamic.missing\n";
    for dialect in [AnalysisDialect::Python, AnalysisDialect::SoacStrictV1] {
        let db = database(ordinary, dialect, false);
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        assert!(
            ty_python_semantic::Db::check_file(&db, file)
                .iter()
                .any(|diagnostic| {
                    diagnostic.id().is_lint_named("unresolved-attribute")
                        && diagnostic.severity() == ruff_db::diagnostic::Severity::Error
                })
        );
        if dialect == AnalysisDialect::SoacStrictV1 {
            let facts =
                export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default())
                    .unwrap();
            assert_eq!(facts.source_dialect, SourceDialect::OrdinaryPython);
            assert!(facts.diagnostics.iter().any(|diagnostic| {
                diagnostic.code == DiagnosticCode::CheckerError
                    && diagnostic.severity == DiagnosticSeverity::Error
            }));
            assert!(!codes(&facts).contains(&DiagnosticCode::StrictUncheckedDynamicType));
        }
    }
}

#[test]
fn soac_strict_framework_attribute_fallback_is_deterministic_between_databases() {
    let source = "from __future__ import strict\nclass Meta(type): pass\nclass Dynamic(metaclass=Meta): pass\nVALUE = Dynamic.missing()\n";
    let export = |unrelated| {
        let db = database(source, AnalysisDialect::SoacStrictV1, unrelated);
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap()
    };
    let facts = export(false);
    assert_eq!(facts, export(true));
    assert_eq!(
        codes(&facts),
        vec![DiagnosticCode::StrictUncheckedDynamicType]
    );
}

#[test]
fn soac_strict_framework_attribute_fallback_does_not_follow_any_or_ignores() {
    let source = "from __future__ import strict\nfrom typing import Any\nclass Ignored:\n    def unavailable(self):\n        return self.missing  # ty: ignore[unresolved-attribute]\nRESULT = Ignored.other\ndef any_value(value: Any): return value.missing()\n";
    let facts = analyze(source, ResolvedStrictPolicy::default());
    let ignored = facts
        .classes
        .iter()
        .find(|class| class.identity.lexical_qualname == "Ignored")
        .unwrap();
    assert!(
        matches!(&ignored.participation, ParticipationProposal::Dynamic(reasons)
        if reasons.contains(&DynamicClassReason::IgnoredDiagnostic))
    );
    let start = source.find("Ignored.other").unwrap() as u32;
    let range = SourceRange::new(start, start + "Ignored.other".len() as u32);
    assert!(facts.diagnostics.iter().any(|diagnostic| {
        diagnostic.source_range == range
            && diagnostic.code == DiagnosticCode::CheckerError
            && diagnostic.severity == DiagnosticSeverity::Error
            && !diagnostic.suppressed
    }));
    assert!(!facts.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == DiagnosticCode::StrictUncheckedDynamicType && !diagnostic.suppressed
    }));
    let any = facts
        .attribute_sites
        .iter()
        .find(|site| site.identity.enclosing_function.lexical_qualname == "any_value")
        .unwrap();
    assert_eq!(any.receiver_type, StaticType::Any);
    assert!(any.uncertainty.contains(&UncertaintyReason::Any));
}

#[test]
fn soac_strict_globals_follow_lexical_mutability_and_sealing() {
    let facts = analyze(
        "from __future__ import strict\nLIMIT = 1\nLIMIT = 2\nglobal mutable_count\nmutable_count = 0\nnamespace = globals()\nglobals()['LIMIT'] = 3\ndef allowed():\n    global mutable_count, added_mutable\n    mutable_count += 1\n    globals()['new_name'] = 1\ndef invalid():\n    namespace['LIMIT'] = 4\n    del globals()['LIMIT']\n    globals().update(LIMIT=5)\n",
        ResolvedStrictPolicy::default(),
    );
    assert_eq!(
        facts
            .global_bindings
            .iter()
            .find(|binding| binding.name == "mutable_count")
            .unwrap()
            .mutability,
        GlobalMutability::ExplicitlyMutable
    );
    assert_eq!(
        facts
            .global_bindings
            .iter()
            .find(|binding| binding.name == "added_mutable")
            .unwrap()
            .mutability,
        GlobalMutability::ExplicitlyMutable
    );
    assert_eq!(
        facts
            .global_bindings
            .iter()
            .find(|binding| binding.name == "LIMIT")
            .unwrap()
            .mutability,
        GlobalMutability::FinalAfterSeal
    );
    assert_eq!(
        codes(&facts)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictFinalGlobalRebind)
            .count(),
        2
    );
    assert_eq!(
        codes(&facts)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictFinalGlobalDelete)
            .count(),
        1
    );
}

#[test]
fn soac_strict_globals_use_resolved_callable_and_module_provenance() {
    let facts = analyze(
        "from __future__ import strict\nimport external_strict as external\nLIMIT = 1\ndef holder(): pass\ndef invalid():\n    holder.__globals__['LIMIT'] = 2\n    external.LIMIT = 3\n    external.__dict__['LIMIT'] = 4\n    vars(external)['LIMIT'] = 5\n    external.mutable = 6\ndef ordinary():\n    def globals() -> dict[str, int]: return {}\n    globals()['LIMIT'] = 2\ndef uncertain(condition):\n    alias = globals() if condition else {}\n    alias['LIMIT'] = 1\n",
        ResolvedStrictPolicy::default(),
    );
    assert_eq!(
        codes(&facts)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictFinalGlobalRebind)
            .count(),
        4
    );
}

#[test]
fn soac_strict_method_classvar_and_class_writes_include_builtin_setters() {
    let facts = analyze(
        "from __future__ import strict\nfrom typing import ClassVar\nclass C:\n    value: int\n    shared: ClassVar[int] = 0\n    def method(self) -> int: return 1\ndef invalid(value: C):\n    value.method = lambda: 1\n    value.shared = 1\n    setattr(value, 'method', lambda: 1)\n    object.__setattr__(value, 'shared', 2)\n    C.method = lambda self: 1\n    del C.value\n    value.__dict__['method'] = lambda: 1\n",
        ResolvedStrictPolicy::default(),
    );
    assert_eq!(
        codes(&facts)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictInstanceMethodShadow)
            .count(),
        2
    );
    assert_eq!(
        codes(&facts)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictClassvarInstanceWrite)
            .count(),
        2
    );
    assert_eq!(
        codes(&facts)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictClassMutation)
            .count(),
        2
    );
}

#[test]
fn soac_strict_self_store_cannot_create_permission_to_shadow_a_method() {
    let facts = analyze(
        "from __future__ import strict\nclass C:\n    def method(self) -> int: return 1\n    def change(self):\n        self.method = lambda: 1\n",
        ResolvedStrictPolicy::default(),
    );
    assert!(codes(&facts).contains(&DiagnosticCode::StrictInstanceMethodShadow));
}

#[test]
fn soac_strict_declared_fields_override_inherited_non_data_methods() {
    let facts = analyze(
        "from __future__ import strict\nfrom typing import Callable\nclass Base:\n    def method(self) -> int: return 1\nclass Child(Base):\n    method: Callable[[], int]\ndef allowed(value: Child):\n    value.method = lambda: 2\n",
        ResolvedStrictPolicy::default(),
    );
    assert!(!codes(&facts).contains(&DiagnosticCode::StrictInstanceMethodShadow));
}

#[test]
fn soac_strict_checked_field_rule_is_gated_by_shared_policy() {
    let source = "from __future__ import strict\nclass C:\n    value: int\ndef invalid(value: C):\n    value.value = 'wrong'\n";
    let default = analyze(source, ResolvedStrictPolicy::default());
    assert!(!codes(&default).contains(&DiagnosticCode::StrictIncompatibleFieldWrite));
    let mut policy = ResolvedStrictPolicy::default();
    policy.checked_fields = CheckedFieldPolicy::SupportedAnnotations;
    let checked = analyze(source, policy);
    assert!(codes(&checked).contains(&DiagnosticCode::StrictIncompatibleFieldWrite));

    let source = "from __future__ import strict\nclass C:\n    def __init__(self, source: int):\n        self.inferred = source\n        self.explicit: int = source\ndef invalid(value: C):\n    value.inferred = 'ordinary inferred field'\n    value.explicit = 'wrong'\n";
    let mut policy = ResolvedStrictPolicy::default();
    policy.checked_fields = CheckedFieldPolicy::SupportedAnnotations;
    let checked = analyze(source, policy);
    let diagnostics = checked
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::StrictIncompatibleFieldWrite)
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics.len(),
        1,
        "inference cannot select a mandatory field contract"
    );
    let start = source.find("value.explicit =").unwrap() as u32;
    assert_eq!(
        diagnostics[0].source_range,
        SourceRange::new(start, start + "value.explicit".len() as u32)
    );
}

#[test]
fn soac_strict_finality_and_overrides_use_checker_class_and_callable_queries() {
    let source = "from __future__ import strict\nfrom typing import final\n@final\nclass FinalBase: pass\nclass BadSubclass(FinalBase): pass\nclass Base:\n    @final\n    def method(self, x: int) -> str: return ''\nclass BadOverride(Base):\n    def method(self, x: str) -> str: return x\nclass OpenBase:\n    def method(self, x: int) -> object: return x\nclass Compatible(OpenBase):\n    def method(self, x: object) -> str: return ''\n";
    let enforced = analyze(source, ResolvedStrictPolicy::default());
    assert!(codes(&enforced).contains(&DiagnosticCode::StrictFinalClassSubclass));
    assert!(codes(&enforced).contains(&DiagnosticCode::StrictFinalMethodOverride));
    assert_eq!(
        codes(&enforced)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictIncompatibleOverride)
            .count(),
        1
    );
    let mut policy = ResolvedStrictPolicy::default();
    policy.typing_final_policy = TypingFinalPolicy::Advisory;
    let advisory = analyze(source, policy);
    assert!(!codes(&advisory).contains(&DiagnosticCode::StrictFinalClassSubclass));
    assert!(!codes(&advisory).contains(&DiagnosticCode::StrictFinalMethodOverride));
}

#[test]
fn soac_strict_automatic_dynamic_fallback_does_not_reject_framework_mutations() {
    let facts = analyze(
        "from __future__ import strict\nclass Meta(type): pass\nclass Dynamic(metaclass=Meta):\n    def method(self) -> int: return 1\nclass Child(Dynamic): pass\ndef allowed(value: Child):\n    value.method = lambda: 2\n    Dynamic.method = lambda self: 3\n",
        ResolvedStrictPolicy::default(),
    );
    assert!(codes(&facts).is_empty());
    assert!(
        facts
            .classes
            .iter()
            .filter(|class| matches!(
                class.identity.lexical_qualname.as_str(),
                "Dynamic" | "Child"
            ))
            .all(|class| matches!(class.participation, ParticipationProposal::Dynamic(_)))
    );
}

#[test]
fn soac_strict_final_base_barriers_also_apply_to_dynamic_children() {
    let facts = analyze(
        "from __future__ import strict\nfrom typing import final\nclass Meta(type): pass\n@final\nclass FinalBase: pass\nclass DynamicChild(FinalBase, metaclass=Meta): pass\nclass Base:\n    @final\n    def method(self) -> int: return 1\nclass DynamicOverride(Base, metaclass=Meta):\n    def method(self) -> int: return 2\n",
        ResolvedStrictPolicy::default(),
    );
    assert_eq!(
        codes(&facts)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictFinalClassSubclass)
            .count(),
        1
    );
    assert_eq!(
        codes(&facts)
            .iter()
            .filter(|code| **code == DiagnosticCode::StrictFinalMethodOverride)
            .count(),
        1
    );
    assert!(!codes(&facts).contains(&DiagnosticCode::StrictIncompatibleOverride));
}

#[test]
fn soac_strict_lints_are_registered_and_ignored_rules_retain_uncertainty() {
    let source = "from __future__ import strict\nclass C:\n    def method(self) -> int: return 1\ndef ignored(value: C):\n    value.method = lambda: 2  # ty: ignore[strict-instance-method-shadow]\n";
    let facts = analyze(source, ResolvedStrictPolicy::default());
    assert!(facts.diagnostics.iter().any(|diagnostic| diagnostic.code
        == DiagnosticCode::StrictInstanceMethodShadow
        && diagnostic.suppressed));
    let db = database_with_options(
        "from __future__ import strict\nLIMIT=1\ndef ignored(): globals()['LIMIT']=2\n",
        AnalysisDialect::SoacStrictV1,
        false,
        "[rules]\nstrict-final-global-rebind = 'ignore'\n",
    );
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(facts.diagnostics.iter().any(|diagnostic| diagnostic.code
        == DiagnosticCode::StrictFinalGlobalRebind
        && diagnostic.suppressed));
}

#[test]
fn soac_strict_mutation_rules_do_not_leak_to_ordinary_python() {
    let facts = analyze(
        "class C:\n    def method(self) -> int: return 1\nLIMIT=1\ndef ordinary(value:C):\n    globals()['LIMIT']=2\n    value.method=lambda:2\n",
        ResolvedStrictPolicy::default(),
    );
    assert!(codes(&facts).is_empty());
}

#[test]
fn soac_strict_used_ignore_is_not_reported_unused_by_export() {
    let source = "from __future__ import strict\nLIMIT = 1\ndef ignored():\n    globals()['LIMIT'] = 2  # ty: ignore[strict-final-global-rebind]\n";
    let db = database_with_options(
        source,
        AnalysisDialect::SoacStrictV1,
        false,
        "[rules]\nunused-ignore-comment = 'error'\n",
    );
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(facts.diagnostics.iter().any(|diagnostic| diagnostic.code
        == DiagnosticCode::StrictFinalGlobalRebind
        && diagnostic.suppressed));
    assert!(
        !facts
            .diagnostics
            .iter()
            .any(
                |diagnostic| diagnostic.severity == DiagnosticSeverity::Error
                    && !diagnostic.suppressed
            )
    );
    // Export does not mutate the ordinary checker or cache its extra suppression usage.
    assert!(
        ty_python_semantic::Db::check_file(&db, file)
            .iter()
            .any(|diagnostic| diagnostic.severity() == ruff_db::diagnostic::Severity::Error)
    );

    let db = database_with_options(
        "from __future__ import strict\nLIMIT = 1  # ty: ignore[strict-final-global-rebind]\n",
        AnalysisDialect::SoacStrictV1,
        false,
        "[rules]\nunused-ignore-comment = 'error'\n",
    );
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(
        facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == DiagnosticCode::CheckerError
                && diagnostic.severity == DiagnosticSeverity::Error
                && !diagnostic.suppressed)
    );
}
