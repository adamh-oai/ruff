//! Structured integration tests through the actual configured project database.

use ruff_db::files::system_path_to_file;
use ruff_db::system::{SystemPathBuf, TestSystem};
use soac_contracts::*;
use ty_python_core::AnalysisDialect;
use ty_python_semantic::{export_soac_module, export_soac_module_facts};

use crate::{ProjectDatabase, ProjectMetadata};

pub(super) fn database(source: &str, dialect: AnalysisDialect, unrelated: bool) -> ProjectDatabase {
    database_with_options(source, dialect, unrelated, "")
}

pub(super) fn database_with_options(
    source: &str,
    dialect: AnalysisDialect,
    unrelated: bool,
    options: &str,
) -> ProjectDatabase {
    let system = TestSystem::default();
    let project = SystemPathBuf::from("/project");
    let config = format!("[environment]\npython-version = '3.15'\n{options}");
    system
        .memory_file_system()
        .write_files_all([
            (project.join("ty.toml"), config.as_str()),
            (project.join("main.py"), source),
            (project.join("unrelated.py"), "class Unrelated: pass\n"),
            (
                project.join("external.py"),
                "class Foreign:\n    def method(self) -> int:\n        return 1\n",
            ),
            (
                project.join("external_strict.py"),
                "from __future__ import strict\nLIMIT = 1\nglobal mutable\nmutable = 0\n",
            ),
            (
                project.join("configuration_values.py"),
                "from nested_values import NUMBER\n",
            ),
            (project.join("nested_values.py"), "NUMBER = 42\n"),
        ])
        .unwrap();
    let metadata = ProjectMetadata::discover(&project, &system).unwrap();
    let db = ProjectDatabase::fallible_with_analysis_dialect(metadata, system, dialect).unwrap();
    if unrelated {
        let file = system_path_to_file(&db, "/project/unrelated.py").unwrap();
        let _ = ty_python_semantic::Db::check_file(&db, file);
    }
    db
}

fn export_from(db: &ProjectDatabase) -> ModuleTypeFacts {
    let file = system_path_to_file(db, "/project/main.py").unwrap();
    let exported = export_soac_module(db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    let mut facts = exported.facts;
    facts.consumed_dependencies = exported
        .dependencies
        .into_iter()
        .map(|dependency| DependencyFingerprint {
            module: dependency.module,
            source_digest: dependency.source_digest,
            source_size: dependency.source_size,
            import_resolution: Fingerprint::digest(format!("{:?}", dependency.path)),
            effective_configuration: Fingerprint::digest(
                "test database: Python 3.15, strict dialect",
            ),
            strict_policy: None,
            type_contract: None,
        })
        .collect();
    let facts = facts.canonicalized().unwrap();
    let source = ruff_db::source::source_text(db, file);
    validate_module_facts(&facts, Some(source.as_bytes())).unwrap();
    facts
}

fn export(source: &str) -> ModuleTypeFacts {
    export_from(&database(source, AnalysisDialect::SoacStrictV1, false))
}

fn class<'a>(facts: &'a ModuleTypeFacts, name: &str) -> &'a ClassTypeFact {
    facts
        .classes
        .iter()
        .find(|class| class.identity.lexical_qualname == name)
        .unwrap()
}

fn function<'a>(facts: &'a ModuleTypeFacts, name: &str) -> &'a FunctionTypeFact {
    facts
        .functions
        .iter()
        .find(|function| function.identity.lexical_qualname == name)
        .unwrap()
}

#[test]
fn soac_nominal_quoted_annotations_reuse_semantic_scopes_and_leaf_identities() {
    let source = r#""""Original δ bytes"""
from __future__ import strict
from typing import Optional, Union
class Recording:
    def __enter__(self) -> "Recording":
        return self
Alias = Recording
def use_context(manager: "Recording") -> "Recording":
    return manager
def combine(first: "Recording | Alias", second: Optional["Recording"]) -> "Union[Recording, Alias]":
    return first
def factory():
    class Local:
        def direct(self, value: "Local") -> "Local":
            return value
    CapturedAlias = Local
    def deferred(value: "CapturedAlias") -> "CapturedAlias":
        return value
    return Local, deferred
"#;
    let facts = export(source);
    assert_eq!(
        facts,
        export_from(&database(source, AnalysisDialect::SoacStrictV1, true))
    );
    for (name, count) in [
        ("Recording.__enter__", 1),
        ("use_context", 2),
        ("combine", 5),
    ] {
        let function = function(&facts, name);
        let leaves: Vec<_> = facts
            .nominal_bindings
            .iter()
            .filter(|leaf| leaf.function == function.identity)
            .collect();
        assert_eq!(leaves.len(), count, "{name}");
        assert!(
            leaves
                .iter()
                .all(|leaf| leaf.binding_scope == facts.module_body_identity())
        );
    }
    let direct = function(&facts, "factory.<locals>.Local.direct");
    let deferred = function(&facts, "factory.<locals>.deferred");
    let local = class(&facts, "factory.<locals>.Local");
    let factory = function(&facts, "factory");
    for (function, direct_binding) in [(direct, true), (deferred, false)] {
        let leaves: Vec<_> = facts
            .nominal_bindings
            .iter()
            .filter(|leaf| leaf.function == function.identity)
            .collect();
        assert_eq!(leaves.len(), 2);
        for leaf in leaves {
            assert_eq!(leaf.binding_scope, factory.identity);
            assert_eq!(leaf.class.definition, local.identity);
            assert_eq!(leaf.binding == local.identity, direct_binding);
        }
    }
    for leaf in &facts.nominal_bindings {
        assert_eq!(
            &source[leaf.expression_range.start as usize..leaf.expression_range.end as usize],
            leaf.name
        );
    }
    assert!(
        !facts
            .diagnostics
            .iter()
            .any(
                |diagnostic| diagnostic.severity == DiagnosticSeverity::Error
                    && !diagnostic.suppressed
            )
    );
}

#[test]
fn soac_nominal_quoted_annotations_do_not_guess_unsupported_expressions() {
    let source = r#"from __future__ import strict
class Recording: pass
def factory(): return Recording
def unsupported(value: "list[Recording]"): pass
def dynamic(value: "factory()"): pass
def escaped(value: "Recor\x64ing"): pass
def raw(value: r"Recording"): pass
def concatenated(value: "Record" "ing"): pass
"#;
    let db = database(source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(facts.nominal_bindings.is_empty());
    assert!(
        facts.diagnostics.iter().any(
            |diagnostic| diagnostic.severity == DiagnosticSeverity::Error && !diagnostic.suppressed
        )
    );
}

#[test]
fn soac_nominal_bindings_preserve_semantic_aliases_slots_and_union_leaves() {
    let source = "from __future__ import strict\nfrom typing import Optional, Union\nfrom external import Foreign as Alias\nclass Local: pass\nLocalAlias = Local\ndef combine(a: Local, b: Alias, c: Optional[LocalAlias], d: Union[Local, Alias]) -> Local | Alias:\n    return a\ndef duplicate(value: Local | LocalAlias) -> Local:\n    return value\n";
    let facts = export(source);
    let combine = function(&facts, "combine");
    let bindings: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|binding| binding.function == combine.identity)
        .collect();
    assert_eq!(bindings.len(), 7);
    for binding in &bindings {
        assert_eq!(binding.binding_scope, facts.module_body_identity());
        assert_eq!(
            &source[binding.expression_range.start as usize..binding.expression_range.end as usize],
            binding.name
        );
    }
    let alias = bindings
        .iter()
        .find(|binding| binding.annotation == AnnotationTarget::Parameter { index: 1 })
        .unwrap();
    assert_eq!(alias.name, "Alias");
    assert_eq!(alias.binding.module, facts.module);
    assert_eq!(alias.binding.definition_kind, DefinitionKind::Assignment);
    assert_eq!(alias.class.definition.module.module_name, "external");
    assert_eq!(alias.class.definition.lexical_qualname, "Foreign");
    let local_alias = bindings
        .iter()
        .find(|binding| binding.annotation == AnnotationTarget::Parameter { index: 2 })
        .unwrap();
    assert_eq!(local_alias.name, "LocalAlias");
    assert_ne!(local_alias.binding, local_alias.class.definition);

    let duplicate = function(&facts, "duplicate");
    assert!(matches!(
        duplicate.signature.parameters[0].value_type,
        StaticType::NominalClass(_)
    ));
    let leaves: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|binding| {
            binding.function == duplicate.identity
                && binding.annotation == AnnotationTarget::Parameter { index: 0 }
        })
        .collect();
    assert_eq!(leaves.len(), 2);
    assert_eq!(leaves[0].class, leaves[1].class);
    assert_ne!(leaves[0].binding, leaves[1].binding);
    assert_ne!(leaves[0].expression_range, leaves[1].expression_range);
    assert_eq!(
        facts,
        export_from(&database(source, AnalysisDialect::SoacStrictV1, true))
    );
}

#[test]
fn soac_nominal_bindings_use_actual_lexical_scopes_and_remove_ignored_contracts() {
    let source = "from __future__ import strict\nfrom typing import Any\nclass Root: pass\nclass Container:\n    Alias = Root\n    def method(self, value: Alias) -> Root:\n        return value\ndef outer():\n    class Nested: pass\n    Alias = Nested\n    def inner(a: Nested, b: Alias) -> Nested:\n        return a\n    return inner\ndef ignored(value: Root) -> Root:\n    return 1  # ty: ignore[invalid-return-type]\ndef unsupported(value: list[Root], dynamic: Any):\n    pass\n";
    let facts = export(source);
    let method = function(&facts, "Container.method");
    let local = facts
        .nominal_bindings
        .iter()
        .find(|binding| {
            binding.function == method.identity
                && binding.annotation == AnnotationTarget::Parameter { index: 1 }
        })
        .unwrap();
    assert_eq!(local.binding_scope, class(&facts, "Container").identity);
    assert_eq!(local.binding.definition_kind, DefinitionKind::Assignment);
    let outer = function(&facts, "outer");
    let inner = function(&facts, "outer.<locals>.inner");
    let inner_bindings: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|binding| binding.function == inner.identity)
        .collect();
    assert_eq!(inner_bindings.len(), 3);
    assert!(
        inner_bindings
            .iter()
            .all(|binding| binding.binding_scope == outer.identity)
    );
    for name in ["ignored", "unsupported"] {
        assert!(
            facts
                .nominal_bindings
                .iter()
                .all(|binding| binding.function != function(&facts, name).identity)
        );
    }
    assert!(
        facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.suppressed)
    );
}

#[test]
fn soac_nominal_bindings_distinguish_factory_aliases_from_direct_class_bindings() {
    let source = "from __future__ import strict\ndef factory():\n    class Local:\n        def direct(self, value: Local) -> Local:\n            return value\n        def alias(self, value: Alias) -> Alias:\n            return value\n    Alias = Local\n    First = Local\n    Second = Local\n    def two(first: First, second: Second) -> Second:\n        return second\n    def either(value: First | Second) -> First | Second:\n        return value\n    return Local, two, either\n";
    let facts = export(source);
    let direct = function(&facts, "factory.<locals>.Local.direct");
    let alias = function(&facts, "factory.<locals>.Local.alias");
    let local = class(&facts, "factory.<locals>.Local");
    let direct_leaves: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|leaf| leaf.function == direct.identity)
        .collect();
    assert_eq!(direct_leaves.len(), 2);
    assert!(direct_leaves.iter().all(|leaf| {
        leaf.binding == local.identity && leaf.binding_scope == function(&facts, "factory").identity
    }));
    let alias_leaves: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|leaf| leaf.function == alias.identity)
        .collect();
    assert_eq!(alias_leaves.len(), 2);
    assert!(alias_leaves.iter().all(|leaf| {
        leaf.class.definition == local.identity
            && leaf.binding != local.identity
            && leaf.binding_scope == function(&facts, "factory").identity
    }));
    let two = function(&facts, "factory.<locals>.two");
    assert_eq!(
        two.signature.parameters[0].value_type,
        two.signature.parameters[1].value_type
    );
    let leaves: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|leaf| leaf.function == two.identity)
        .collect();
    assert_eq!(leaves.len(), 3);
    assert_eq!(leaves[0].class, leaves[1].class);
    assert_ne!(leaves[0].binding, leaves[1].binding);
    let either = function(&facts, "factory.<locals>.either");
    assert!(matches!(
        either.signature.parameters[0].value_type,
        StaticType::NominalClass(_)
    ));
    let leaves: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|leaf| leaf.function == either.identity)
        .collect();
    assert_eq!(leaves.len(), 4);
}

#[test]
fn soac_nominal_factory_call_unknowns_do_not_gain_lexical_binding_plans() {
    let source = "from __future__ import strict\ndef factory():\n    class Local: pass\n    return Local\nAlias = factory()\ndef unchecked(value: Alias) -> Alias:\n    return value\n";
    let facts = export(source);
    let unchecked = function(&facts, "unchecked");
    assert_eq!(
        unchecked.signature.parameters[0].value_type,
        StaticType::Unknown
    );
    assert_eq!(unchecked.signature.return_type, StaticType::Unknown);
    assert!(facts.nominal_bindings.is_empty());
}

#[test]
fn soac_export_is_owned_deterministic_and_preserves_original_byte_identities() {
    let source = "\"\"\"δ original bytes\"\"\"\nfrom __future__ import strict\nfrom typing import final\n@final\nclass Leaf:\n    value: int\n    def method(self, x: float) -> int:\n        return 1\ndef outer():\n    class Nested:\n        value: str\n    return Nested\n";
    let one = export_from(&database(source, AnalysisDialect::SoacStrictV1, false));
    let two = export_from(&database(source, AnalysisDialect::SoacStrictV1, true));
    assert_eq!(
        one, two,
        "independent Salsa allocation histories must not escape"
    );
    assert_eq!(
        one.module.source_hash,
        legacy_source_hash(source.as_bytes())
    );
    assert_eq!(one.source_digest, Fingerprint::digest(source.as_bytes()));
    assert_eq!(one.source_size, source.len() as u32);
    assert_eq!(class(&one, "Leaf").openness, ClassOpenness::DeclaredFinal);
    assert_eq!(
        class(&one, "Leaf").participation,
        ParticipationProposal::Candidate
    );
    assert_eq!(
        class(&one, "outer.<locals>.Nested")
            .identity
            .definition_kind,
        DefinitionKind::Class
    );
    let parameter = &function(&one, "Leaf.method").signature.parameters[1];
    assert_eq!(parameter.annotation_origin, AnnotationOrigin::Explicit);
    assert!(
        matches!(&parameter.value_type, StaticType::NumericWidening { target: BuiltinType::Float, accepted } if accepted.contains(&BuiltinType::Int))
    );
    assert!(matches!(
        &class(&one, "Leaf").instance_fields[0].value_type,
        StaticType::NominalBuiltin {
            builtin: BuiltinType::Int,
            allow_subclasses: true
        }
    ));
}

#[test]
fn soac_export_uses_semantic_binding_for_methods_callable_fields_and_open_families() {
    let facts = export(
        "from __future__ import strict\nfrom typing import Callable, final\nclass Receiver:\n    callback: Callable[[int], int]\n    def method(self, x: int) -> int:\n        return x\n    @staticmethod\n    def static(x: int) -> int:\n        return x\n    @classmethod\n    def class_method(cls, x: int) -> int:\n        return x\n    @final\n    def final_method(self) -> int:\n        return 1\ndef invoke(value: Receiver):\n    value.method(1)\n    value.static(2)\n    value.class_method(3)\n    value.callback(4)\n",
    );
    let receiver = class(&facts, "Receiver");
    assert_eq!(receiver.openness, ClassOpenness::OpenSubclassFamily);
    assert_eq!(
        receiver.instance_fields[0].field_kind,
        FieldKind::CallableInstanceField
    );
    for (name, expected) in [
        ("method", MethodBinding::Instance),
        ("static", MethodBinding::Static),
        ("class_method", MethodBinding::Class),
    ] {
        assert_eq!(
            receiver
                .methods
                .iter()
                .find(|method| method.name == name)
                .unwrap()
                .binding,
            expected
        );
    }
    assert!(
        receiver
            .methods
            .iter()
            .find(|method| method.name == "final_method")
            .unwrap()
            .declared_final
    );
    let site = |name| {
        facts
            .call_sites
            .iter()
            .find(|site| site.attribute_name.as_deref() == Some(name))
            .unwrap()
    };
    assert_eq!(site("method").binding, CallBindingFact::BoundInstanceMethod);
    assert_eq!(
        site("method").uncertainty,
        CallUncertainty::OpenSubclassFamily
    );
    assert_eq!(
        site("method").signature.parameters.len(),
        1,
        "checker binding must remove self"
    );
    assert_eq!(
        site("class_method").binding,
        CallBindingFact::BoundClassMethod
    );
    assert_eq!(site("class_method").signature.parameters.len(), 1);
    assert_eq!(site("static").binding, CallBindingFact::StaticMethod);
    assert_eq!(
        site("callback").binding,
        CallBindingFact::CallableInstanceField
    );
    assert_eq!(
        site("callback").uncertainty,
        CallUncertainty::CallableInstanceField
    );
}

#[test]
fn soac_export_generated_parameters_preserve_field_origins_not_display_annotations() {
    let facts = export(
        r#"from __future__ import strict
from dataclasses import dataclass, InitVar
@dataclass(frozen=True)
class Base:
    first: int = 1
@dataclass(frozen=True, order=True)
class Record(Base):
    other: int = 2
    seed: InitVar[int] = 3
    def annotated(self: "Record", other: "Record") -> bool:
        return self is other
"#,
    );
    let record = class(&facts, "Record");
    for name in ["__init__", "__replace__"] {
        let method = record
            .methods
            .iter()
            .find(|method| method.name == name)
            .unwrap();
        assert!(method.generated.is_some());
        assert_eq!(
            method.signature.parameters[0].annotation_origin,
            AnnotationOrigin::Inferred,
            "{name}'s synthetic receiver has a display type, not a source annotation"
        );
        for parameter in method.signature.parameters.iter().skip(1) {
            assert_eq!(
                parameter.annotation_origin,
                AnnotationOrigin::Explicit,
                "{name}.{} must retain its actual dataclass field declaration",
                parameter.name
            );
        }
        assert_eq!(
            method.signature.return_annotation_origin,
            AnnotationOrigin::Inferred
        );
    }
    for name in [
        "__lt__",
        "__le__",
        "__gt__",
        "__ge__",
        "__setattr__",
        "__delattr__",
    ] {
        let method = record
            .methods
            .iter()
            .find(|method| method.name == name)
            .unwrap();
        assert!(method.generated.is_some());
        assert!(
            method
                .signature
                .parameters
                .iter()
                .all(|parameter| parameter.annotation_origin == AnnotationOrigin::Inferred),
            "{name}'s synthesized display annotations are not source contracts"
        );
    }
    let annotated = function(&facts, "Record.annotated");
    assert!(
        annotated
            .signature
            .parameters
            .iter()
            .all(|parameter| parameter.annotation_origin == AnnotationOrigin::Explicit),
        "actual source-written receiver and comparison annotations remain explicit"
    );
    assert!(
        record
            .instance_fields
            .iter()
            .all(|field| field.annotation_origin == AnnotationOrigin::Explicit)
    );
}

#[test]
fn soac_export_uses_checker_dataclass_fields_options_and_synthesized_signature() {
    let facts = export(
        "from __future__ import strict\nfrom dataclasses import dataclass, field, InitVar\nfrom typing import ClassVar\n@dataclass\nclass Base:\n    first: int = 1\n@dataclass(slots=True, kw_only=True)\nclass Child(Base):\n    value: str = 'x'\n    temporary: InitVar[int] = 2\n    shared: ClassVar[int] = 3\n    items: list[int] = field(default_factory=list)\n",
    );
    let child = class(&facts, "Child");
    assert!(
        child
            .instance_fields
            .iter()
            .all(|field| { field.annotation_origin == AnnotationOrigin::Explicit }),
        "inherited and generated dataclass fields retain their actual declaration origin"
    );
    let transform = child.transform.as_ref().unwrap();
    assert_eq!(transform.kind, TransformKind::StdlibDataclass);
    let options = transform.dataclass_options.as_ref().unwrap();
    assert!(options.slots && options.kw_only);
    assert_eq!(child.dictionary, ClassDictionarySemantics::ExplicitSlots);
    let field = |name| {
        child
            .instance_fields
            .iter()
            .find(|field| field.name == name)
            .unwrap()
    };
    assert_eq!(
        field("first").declaring_class.definition.lexical_qualname,
        "Base"
    );
    assert_eq!(field("temporary").field_kind, FieldKind::InitOnly);
    assert_eq!(field("shared").field_kind, FieldKind::ClassVariable);
    assert!(matches!(
        field("items").default,
        DefaultFact::Factory { .. }
    ));
    assert!(matches!(
        field("items").value_type,
        StaticType::Unsupported {
            kind: UnsupportedTypeKind::MutableGeneric,
            ..
        }
    ));
    let init = child
        .methods
        .iter()
        .find(|method| method.name == "__init__")
        .unwrap();
    assert!(init.implementation.is_none() && init.generated.is_some());
    assert!(
        init.signature
            .parameters
            .iter()
            .any(|parameter| parameter.name == "value"
                && parameter.kind == ParameterKind::KeywordOnly)
    );
    assert!(
        !init
            .signature
            .parameters
            .iter()
            .any(|parameter| parameter.name == "shared")
    );
}

#[test]
fn soac_export_field_contract_origin_comes_from_semantic_declarations_not_inferred_types() {
    let source = r#"from __future__ import strict
from typing import Any, Final
class Model:
    class_body: int
    defaulted: int = 0
    inferred_default = 0
    def __init__(self, source: int):
        self.explicit_self: int = source
        self.inferred_from_parameter = source
        self.inferred_from_literal = 1
        self.inferred_default = source
        self.explicit_any: Any = source
        self.bare_final: Final = source
        self.final_annotation: Final[int] = source
        self.uninitialized: str
"#;
    let one = export_from(&database(source, AnalysisDialect::SoacStrictV1, false));
    let two = export_from(&database(source, AnalysisDialect::SoacStrictV1, true));
    assert_eq!(one, two);
    let model = class(&one, "Model");
    let field = |name| {
        model
            .instance_fields
            .iter()
            .find(|field| field.name == name)
            .unwrap()
    };
    for name in [
        "class_body",
        "defaulted",
        "explicit_self",
        "explicit_any",
        "final_annotation",
        "uninitialized",
    ] {
        assert_eq!(
            field(name).annotation_origin,
            AnnotationOrigin::Explicit,
            "{name}"
        );
    }
    for name in [
        "inferred_from_parameter",
        "inferred_from_literal",
        "inferred_default",
        "bare_final",
    ] {
        assert_eq!(
            field(name).annotation_origin,
            AnnotationOrigin::Inferred,
            "{name}"
        );
    }
    assert_eq!(field("explicit_any").value_type, StaticType::Any);
    assert_eq!(
        field("explicit_self").value_type,
        field("inferred_from_parameter").value_type
    );
    assert_eq!(
        function(&one, "Model.__init__").signature.parameters[1].annotation_origin,
        AnnotationOrigin::Explicit,
        "an annotated constructor argument does not manufacture a field annotation",
    );
}

#[test]
fn soac_export_construction_callbacks_remain_candidates_without_instance_hook_authority() {
    let facts = export(
        r#"from __future__ import strict
class Base:
    def __init_subclass__(cls):
        pass
class Child(Base):
    value: int = 7
class Named:
    def __set_name__(self, owner, name):
        pass
class AttributeHook:
    def __getattribute__(self, name):
        return object.__getattribute__(self, name)
class InheritedAttributeHook(AttributeHook):
    pass
"#,
    );
    for name in ["Base", "Child", "Named"] {
        assert_eq!(
            class(&facts, name).participation,
            ParticipationProposal::Candidate,
            "{name}"
        );
    }
    let hook = class(&facts, "Base")
        .methods
        .iter()
        .find(|method| method.name == "__init_subclass__")
        .unwrap();
    assert_eq!(hook.binding, MethodBinding::Class);
    assert!(hook.implementation.is_some());
    assert!(
        hook.signature
            .parameters
            .iter()
            .all(|parameter| { parameter.annotation_origin != AnnotationOrigin::Explicit })
    );
    for name in ["AttributeHook", "InheritedAttributeHook"] {
        assert!(
            matches!(
                &class(&facts, name).participation,
                ParticipationProposal::Dynamic(reasons)
                    if reasons.contains(&DynamicClassReason::CustomAttributeHooks)
            ),
            "{name}"
        );
    }
}

#[test]
fn soac_export_preserves_dynamic_uncertainty_protocols_and_framework_fallback() {
    let facts = export(
        "from __future__ import strict\nfrom typing import Any, Protocol\nclass Shape(Protocol):\n    def method(self) -> int: ...\nclass Meta(type): pass\nclass Managed(metaclass=Meta):\n    value: int\ndef decorate(cls):\n    return cls\n@decorate\nclass Wrapped:\n    value: int\ndef uncertain(explicit: Any, implicit, protocol: Shape):\n    explicit.method()\n    implicit.method()\n    protocol.method()\n",
    );
    let managed = class(&facts, "Managed");
    assert!(
        matches!(&managed.participation, ParticipationProposal::Dynamic(reasons) if reasons.contains(&DynamicClassReason::NonParticipatingMetaclass))
    );
    assert!(
        matches!(&class(&facts, "Wrapped").participation, ParticipationProposal::Dynamic(reasons) if reasons.contains(&DynamicClassReason::UnknownDecorator))
    );
    let parameters = &function(&facts, "uncertain").signature.parameters;
    assert_eq!(parameters[0].value_type, StaticType::Any);
    assert_eq!(parameters[1].value_type, StaticType::Unknown);
    assert!(matches!(
        parameters[2].value_type,
        StaticType::StructuralProtocol(_)
    ));
    for site in facts
        .call_sites
        .iter()
        .filter(|site| site.identity.enclosing_function.lexical_qualname == "uncertain")
    {
        assert_ne!(site.uncertainty, CallUncertainty::ExactStaticTarget);
    }
}

#[test]
fn soac_export_ignored_diagnostics_demote_affected_class_but_not_unrelated_class() {
    let facts = export(
        "from __future__ import strict\nclass Damaged:\n    value: int = 'wrong'  # ty: ignore[invalid-assignment]\nclass Fine:\n    value: int = 1\n",
    );
    assert!(
        facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.suppressed)
    );
    assert!(
        matches!(&class(&facts, "Damaged").participation, ParticipationProposal::Dynamic(reasons) if reasons.contains(&DynamicClassReason::IgnoredDiagnostic))
    );
    assert_eq!(
        class(&facts, "Fine").participation,
        ParticipationProposal::Candidate
    );
    assert_eq!(
        class(&facts, "Fine").instance_fields[0].annotation_origin,
        AnnotationOrigin::Explicit
    );
    assert!(matches!(
        class(&facts, "Damaged").instance_fields[0].value_type,
        StaticType::Unknown
    ));
}

#[test]
fn soac_export_requires_explicit_dialect_and_does_not_infer_strictness_from_text() {
    let ordinary = database("class Ordinary: pass\n", AnalysisDialect::Python, false);
    let file = system_path_to_file(&ordinary, "/project/main.py").unwrap();
    assert!(
        export_soac_module_facts(&ordinary, file, "main", ResolvedStrictPolicy::default()).is_err()
    );
    let facts = export("'from __future__ import strict'\nclass Ordinary: pass\n");
    assert_eq!(facts.source_dialect, SourceDialect::OrdinaryPython);
    assert!(matches!(
        class(&facts, "Ordinary").participation,
        ParticipationProposal::Dynamic(_)
    ));
    assert!(
        facts
            .global_bindings
            .iter()
            .all(|binding| binding.mutability == GlobalMutability::Unknown)
    );
}

#[test]
fn soac_export_reports_actual_dependency_sources_not_import_alias_spelling() {
    let source = "from __future__ import strict\nfrom external import Foreign as Alias\ndef use(value: Alias) -> int:\n    return value.method()\n";
    let db = database(source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let exported = export_soac_module(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    let external = exported
        .dependencies
        .iter()
        .find(|dependency| dependency.module.module_name == "external")
        .unwrap();
    assert_eq!(
        external.path,
        ty_python_semantic::SoacDependencyPath::System("/project/external.py".into())
    );
    assert_eq!(
        external.source_digest,
        Fingerprint::digest("class Foreign:\n    def method(self) -> int:\n        return 1\n")
    );
    assert!(exported.dependencies.iter().any(|dependency| matches!(
        dependency.path,
        ty_python_semantic::SoacDependencyPath::Vendored(_)
    )));
    let _ = export_from(&db);
}

#[test]
fn soac_export_inherited_method_targets_refer_to_declaring_class() {
    let facts = export(
        "from __future__ import strict\nclass Base:\n    def method(self) -> int: return 1\nclass Child(Base): pass\ndef use(value: Child):\n    return value.method()\n",
    );
    let call = facts
        .call_sites
        .iter()
        .find(|site| site.attribute_name.as_deref() == Some("method"))
        .unwrap();
    assert!(
        matches!(&call.candidate_targets[0], CallableTargetFact::Method { class, .. } if class.definition.lexical_qualname == "Base")
    );
}

#[test]
fn soac_export_typevars_and_lambda_calls_have_source_binders() {
    let facts = export(
        "from __future__ import strict\ndef identity[T: int](value: T) -> T:\n    return value\ncallback = lambda: identity(1)\n",
    );
    assert!(matches!(
        function(&facts, "identity").signature.parameters[0].value_type,
        StaticType::TypeVariable(_)
    ));
    let call = facts
        .call_sites
        .iter()
        .find(|site| site.identity.enclosing_function.definition_kind == DefinitionKind::Lambda)
        .unwrap();
    assert_eq!(
        call.identity.enclosing_function.lexical_qualname,
        "<lambda>"
    );
}

#[test]
fn soac_export_tracks_imports_even_when_values_normalize_to_builtin_types() {
    let db = database(
        "from __future__ import strict\nfrom configuration_values import NUMBER\nCOPY = NUMBER\n",
        AnalysisDialect::SoacStrictV1,
        false,
    );
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let exported = export_soac_module(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    for name in ["configuration_values", "nested_values"] {
        assert!(
            exported
                .dependencies
                .iter()
                .any(|dependency| dependency.module.module_name == name),
            "missing {name}"
        );
    }
}

#[test]
fn soac_export_unknown_dataclass_options_remain_dynamic() {
    let facts = export(
        "from __future__ import strict\nfrom dataclasses import dataclass\ndef choose() -> bool: return bool(input())\n@dataclass(slots=choose())\nclass Uncertain:\n    value: int\n",
    );
    let class = class(&facts, "Uncertain");
    assert!(matches!(
        class.participation,
        ParticipationProposal::Dynamic(_)
    ));
    assert_eq!(class.dictionary, ClassDictionarySemantics::Unknown);
    assert!(class.transform.is_none());
    assert!(class.decorators[0].arguments.is_empty());
    assert!(
        class.decorators[0]
            .uncertainty
            .contains(&UncertaintyReason::DynamicDecorator)
    );
}

#[test]
fn soac_export_dataclass_field_presence_requires_actual_generated_init() {
    let facts = export(
        "from __future__ import strict\nfrom dataclasses import dataclass\n@dataclass(init=False)\nclass NoInit:\n    value: int\n@dataclass\nclass CustomInit:\n    value: int\n    def __init__(self): pass\n",
    );
    for name in ["NoInit", "CustomInit"] {
        assert_eq!(
            class(&facts, name).instance_fields[0].initialization,
            InitializationPolicy::MayBeAbsent
        );
    }
}

#[test]
fn soac_export_generator_lambdas_are_not_synchronous_functions() {
    let facts = export("from __future__ import strict\ncallback = lambda: (yield 1)\n");
    assert_eq!(
        function(&facts, "<lambda>").function_kind,
        FunctionKind::Generator
    );
}

#[test]
fn soac_export_explicit_interpreter_paths_do_not_guess_from_an_uninstalled_prefix() {
    let system = TestSystem::default();
    system.memory_file_system().write_files_all([
        ("/project/ty.toml", "[environment]\npython-version = '3.15'\npython = '/wrong-prefix'\n"),
        ("/project/main.py", "from __future__ import strict\nfrom selected import Value\ndef identity(value: Value) -> Value: return value\n"),
        ("/selected/python3.15/site-packages/selected.py", "class Value: pass\n"),
        ("/wrong-prefix/lib/python3.12/site-packages/selected.py", "class Wrong: pass\n"),
    ]).unwrap();
    let metadata =
        ProjectMetadata::discover(ruff_db::system::SystemPath::new("/project"), &system).unwrap();
    let db = ProjectDatabase::fallible_with_python_environment(
        metadata,
        system,
        AnalysisDialect::SoacStrictV1,
        crate::metadata::PythonEnvironmentPaths {
            site_packages: vec![SystemPathBuf::from("/selected/python3.15/site-packages")],
            real_stdlib: None,
        },
    )
    .unwrap();
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let export = export_soac_module(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(export.dependencies.iter().any(|dependency| dependency.path
        == ty_python_semantic::SoacDependencyPath::System(
            "/selected/python3.15/site-packages/selected.py".into()
        )));
    assert!(
        !export
            .facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
    );
}

fn inheritance_database(base: &str, unrelated_first: bool) -> (ProjectDatabase, TestSystem) {
    let system = TestSystem::default();
    system.memory_file_system().write_files_all([
        ("/project/ty.toml", "[environment]\npython-version = '3.15'\n"),
        ("/project/base.py", base),
        ("/project/bridge.py", "from __future__ import strict\nfrom base import Base\nclass Middle(Base): pass\n"),
        ("/project/main.py", "from __future__ import strict\nfrom bridge import Middle\nclass Child(Middle):\n    def __init__(self):\n        super().__init__()\n        self.own: int = 3\n"),
        ("/project/ordinary.py", "class Foreign: pass\n"),
        ("/project/unrelated.py", "class Unrelated: pass\n"),
    ]).unwrap();
    let metadata =
        ProjectMetadata::discover(ruff_db::system::SystemPath::new("/project"), &system).unwrap();
    let db = ProjectDatabase::fallible_with_analysis_dialect(
        metadata,
        system.clone(),
        AnalysisDialect::SoacStrictV1,
    )
    .unwrap();
    if unrelated_first {
        let file = system_path_to_file(&db, "/project/unrelated.py").unwrap();
        let _ = ty_python_semantic::Db::check_file(&db, file);
    }
    (db, system)
}

#[test]
fn soac_export_external_strict_bases_are_semantic_proposals_not_mutable_by_location() {
    let source = "from __future__ import strict\nclass Base:\n    def __init__(self):\n        self.inherited: int = 1\n";
    let (first, _) = inheritance_database(source, false);
    let (second, _) = inheritance_database(source, true);
    let facts = export_from(&first);
    assert_eq!(facts, export_from(&second));
    let child = class(&facts, "Child");
    assert_eq!(child.participation, ParticipationProposal::Candidate);
    assert!(child.inheritance.complete);
    assert_eq!(child.bases[0].definition.module.module_name, "bridge");
    let ancestor = child
        .inheritance
        .linearized_bases
        .iter()
        .find(|base| base.definition.module.module_name == "base")
        .unwrap();
    let base_file = system_path_to_file(&first, "/project/base.py").unwrap();
    let base =
        export_soac_module(&first, base_file, "base", ResolvedStrictPolicy::default()).unwrap();
    assert_eq!(ancestor.definition, base.facts.classes[0].identity);
    assert_eq!(ancestor.source_digest, Fingerprint::digest(source));
    assert!(
        facts
            .consumed_dependencies
            .iter()
            .any(|dependency| dependency.module == ancestor.definition.module
                && dependency.source_digest == ancestor.source_digest)
    );
    assert!(!facts.function_has_statically_dynamic_class_owner(
        &child.methods[0].implementation.clone().unwrap()
    ));
    assert_eq!(
        child.instance_fields[0].annotation_origin,
        AnnotationOrigin::Explicit
    );
}

#[test]
fn soac_export_external_strict_bases_propagate_real_dynamic_classification() {
    for source in [
        "class Base: pass\n",
        "from __future__ import strict\nclass Meta(type): pass\nclass Base(metaclass=Meta): pass\n",
        "from __future__ import strict\ndef dynamic[T](value: T) -> T: return value\n@dynamic\nclass Base: pass\n",
        "from __future__ import strict\nclass Base:\n    value: int = 'bad'  # ty: ignore[invalid-assignment]\n",
        "from __future__ import strict\nfrom ordinary import Foreign\nclass Base(Foreign): pass\n",
        "from __future__ import strict\nclass Base:\n    def __getattr__(self, name: str) -> int: return 1\n",
        "from __future__ import strict\nclass Descriptor:\n    def __get__(self, instance, owner): return 1\nclass Base:\n    item = Descriptor()\n",
        // The caller does not know a different file's adapter policy. The
        // importer must not authorize that transform with its own policy.
        "from __future__ import strict\nfrom dataclasses import dataclass\n@dataclass\nclass Base:\n    value: int = 1\n",
    ] {
        let (db, _) = inheritance_database(source, false);
        let facts = export_from(&db);
        let child = class(&facts, "Child");
        assert!(
            matches!(&child.participation, ParticipationProposal::Dynamic(reasons)
            if reasons.contains(&DynamicClassReason::MutableBase)),
            "{source}"
        );
        assert!(
            facts.function_has_statically_dynamic_class_owner(
                &child.methods[0].implementation.clone().unwrap()
            ),
            "{source}"
        );
    }
}

#[test]
fn soac_export_external_base_ignores_remain_scoped_to_the_actual_owner() {
    let source = "from __future__ import strict\nclass Damaged:\n    value: int = 'bad'  # ty: ignore[invalid-assignment]\nclass Base: pass\n";
    let (db, _) = inheritance_database(source, false);
    assert_eq!(
        class(&export_from(&db), "Child").participation,
        ParticipationProposal::Candidate
    );
}

#[test]
fn soac_export_external_base_source_changes_invalidate_transitive_queries() {
    let source = "from __future__ import strict\nclass Base: pass\n";
    let (mut db, system) = inheritance_database(source, false);
    let initial = export_from(&db);
    assert_eq!(
        class(&initial, "Child").participation,
        ParticipationProposal::Candidate
    );
    for changed in [
        "class Base: pass\n",
        "from __future__ import strict\ndef dynamic[T](value: T) -> T: return value\n@dynamic\nclass Base: pass\n",
    ] {
        system
            .memory_file_system()
            .write_file_all("/project/base.py", changed)
            .unwrap();
        db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
            "/project/base.py".into(),
        )]);
        let facts = export_from(&db);
        assert_eq!(facts.module, initial.module);
        assert!(
            matches!(&class(&facts, "Child").participation, ParticipationProposal::Dynamic(reasons)
            if reasons.contains(&DynamicClassReason::MutableBase))
        );
        assert!(
            facts
                .consumed_dependencies
                .iter()
                .any(|dependency| dependency.module.module_name == "base"
                    && dependency.source_digest == Fingerprint::digest(changed))
        );
    }
    system
        .memory_file_system()
        .write_file_all("/project/base.py", source)
        .unwrap();
    db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
        "/project/base.py".into(),
    )]);
    assert_eq!(export_from(&db), initial);
}
