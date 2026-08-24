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
fn soac_export_uses_checker_dataclass_fields_options_and_synthesized_signature() {
    let facts = export(
        "from __future__ import strict\nfrom dataclasses import dataclass, field, InitVar\nfrom typing import ClassVar\n@dataclass\nclass Base:\n    first: int = 1\n@dataclass(slots=True, kw_only=True)\nclass Child(Base):\n    value: str = 'x'\n    temporary: InitVar[int] = 2\n    shared: ClassVar[int] = 3\n    items: list[int] = field(default_factory=list)\n",
    );
    let child = class(&facts, "Child");
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
