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
