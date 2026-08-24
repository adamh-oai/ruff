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

fn export_proposal_from(db: &ProjectDatabase) -> ModuleTypeFacts {
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
    facts.canonicalized().unwrap()
}

fn export_from(db: &ProjectDatabase) -> ModuleTypeFacts {
    let facts = export_proposal_from(db);
    let file = system_path_to_file(db, "/project/main.py").unwrap();
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

fn function_owns_binding(binding: &NominalBindingFact, function: &FunctionTypeFact) -> bool {
    binding
        .owner
        .as_function()
        .is_some_and(|(owner, _)| owner == &function.identity)
}

fn parameter_owns_binding(binding: &NominalBindingFact, index: u32) -> bool {
    binding
        .owner
        .as_function()
        .is_some_and(|(_, annotation)| annotation == AnnotationTarget::Parameter { index })
}

fn field<'a>(facts: &'a ModuleTypeFacts, class_name: &str, name: &str) -> &'a FieldTypeFact {
    class(facts, class_name)
        .instance_fields
        .iter()
        .find(|field| field.name == name)
        .unwrap()
}

fn field_bindings<'a>(
    facts: &'a ModuleTypeFacts,
    field: &FieldTypeFact,
) -> Vec<&'a NominalBindingFact> {
    let reference = field
        .annotation_reference()
        .expect("actual annotated field definition");
    facts.nominal_bindings.iter().filter(|binding| {
        matches!(&binding.owner, NominalBindingOwner::Field { field } if field == &reference)
    }).collect()
}

#[test]
fn soac_nominal_field_bindings_preserve_actual_assignment_and_factory_scope() {
    let source = r#"from __future__ import strict
class GlobalTarget:
    pass
class GlobalHolder:
    value: GlobalTarget
def accept(value: GlobalTarget) -> GlobalTarget:
    return value
def family():
    class Target:
        pass
    class Holder:
        value: Target
        Alias = Target
        class_alias: Alias
        own: Holder | None
    def replace_target(value: type[Target]):
        nonlocal Target
        Target = value
    return Target, Holder, replace_target
"#;
    let facts = export(source);
    assert!(
        facts.diagnostics.iter().all(
            |diagnostic| diagnostic.severity != DiagnosticSeverity::Error || diagnostic.suppressed
        )
    );
    let global = field(&facts, "GlobalHolder", "value");
    let global_definition = global
        .annotation_definition
        .as_ref()
        .expect("class annotation provenance");
    assert_eq!(
        global_definition.definition_kind,
        DefinitionKind::Assignment
    );
    assert_eq!(global_definition.module, facts.module);
    assert_eq!(
        &source[global_definition.source_range.start as usize
            ..global_definition.source_range.end as usize],
        "value: GlobalTarget"
    );
    let global_bindings = field_bindings(&facts, global);
    assert_eq!(global_bindings.len(), 1);
    assert_eq!(
        global_bindings[0].binding,
        class(&facts, "GlobalTarget").identity
    );
    assert_eq!(
        global_bindings[0].binding_scope,
        facts.module_body_identity()
    );
    let function_bindings: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|binding| function_owns_binding(binding, function(&facts, "accept")))
        .collect();
    assert_eq!(function_bindings.len(), 2);
    assert_ne!(global_bindings[0].owner, function_bindings[0].owner);

    let factory = function(&facts, "family");
    let target = class(&facts, "family.<locals>.Target");
    let holder = class(&facts, "family.<locals>.Holder");
    for (name, scope, definition) in [
        ("value", &factory.identity, &target.identity),
        ("own", &factory.identity, &holder.identity),
    ] {
        let field = field(&facts, "family.<locals>.Holder", name);
        let bindings = field_bindings(&facts, field);
        assert_eq!(bindings.len(), 1, "{name}");
        assert_eq!(&bindings[0].binding_scope, scope);
        assert_eq!(&bindings[0].binding, definition);
        assert_eq!(field.declaring_class.definition, holder.identity);
    }
    let class_alias = field_bindings(
        &facts,
        field(&facts, "family.<locals>.Holder", "class_alias"),
    );
    assert_eq!(class_alias.len(), 1);
    assert_eq!(class_alias[0].binding_scope, holder.identity);
    assert_eq!(
        class_alias[0].binding.definition_kind,
        DefinitionKind::Assignment
    );
    assert_ne!(class_alias[0].binding, target.identity);
    assert_eq!(class_alias[0].class.definition, target.identity);
    for binding in &facts.nominal_bindings {
        assert_eq!(
            &source[binding.expression_range.start as usize..binding.expression_range.end as usize],
            binding.name
        );
    }
    assert_eq!(
        facts,
        export_from(&database(source, AnalysisDialect::SoacStrictV1, true))
    );
}

#[test]
fn soac_nominal_field_bindings_preserve_dataclass_declarations_and_semantic_wrappers() {
    let source = r#"from __future__ import strict
from dataclasses import dataclass, InitVar
from typing import Annotated, ClassVar, Optional, Union
class Target:
    pass
Alias = Target
@dataclass
class Base:
    base: Target
    seed: InitVar[Target]
    pair: Union[Target, Alias]
    annotated: Annotated[Target, Alias]
    optional: Optional[Target]
    shared: ClassVar[Target] = Target()
@dataclass
class Child(Base):
    own: Target
"#;
    let facts = export(source);
    assert!(
        facts.diagnostics.iter().all(
            |diagnostic| diagnostic.severity != DiagnosticSeverity::Error || diagnostic.suppressed
        )
    );
    let base = class(&facts, "Base");
    for (name, count) in [
        ("base", 1),
        ("seed", 1),
        ("pair", 2),
        ("annotated", 1),
        ("optional", 1),
        ("shared", 1),
    ] {
        let field = field(&facts, "Base", name);
        assert_eq!(field.annotation_origin, AnnotationOrigin::Explicit);
        assert_eq!(field.declaring_class.definition, base.identity);
        let bindings = field_bindings(&facts, field);
        assert_eq!(bindings.len(), count, "{name}");
        assert!(
            bindings
                .iter()
                .all(|binding| binding.binding_scope == facts.module_body_identity())
        );
        if field.field_kind != FieldKind::ClassVariable {
            assert_eq!(
                field.annotation_reference(),
                self::field(&facts, "Child", name).annotation_reference()
            );
        }
    }
    let pair = field_bindings(&facts, field(&facts, "Base", "pair"));
    assert_eq!(pair[0].class, pair[1].class);
    assert_ne!(pair[0].binding, pair[1].binding);
    assert_ne!(pair[0].expression_range, pair[1].expression_range);
    let own = field(&facts, "Child", "own");
    assert_eq!(
        own.declaring_class.definition,
        class(&facts, "Child").identity
    );
    assert_eq!(field_bindings(&facts, own).len(), 1);
    let generated = base
        .methods
        .iter()
        .find(|method| method.name == "__init__")
        .unwrap();
    assert!(generated.generated.is_some());
    assert!(generated.implementation.is_none());
    assert!(
        facts
            .nominal_bindings
            .iter()
            .all(|binding| matches!(&binding.owner, NominalBindingOwner::Field { .. }))
    );
    assert_eq!(
        facts,
        export_from(&database(source, AnalysisDialect::SoacStrictV1, true))
    );
}

#[test]
fn soac_nominal_field_bindings_distinguish_method_annotations_from_inferred_assignments() {
    let source = r#"from __future__ import strict
class Target:
    pass
class Holder:
    def __init__(self, value: Target):
        self.explicit: Target = value
        self.inferred = value
    def ambiguous_one(self, value):
        self.ambiguous: Target = value
    def ambiguous_two(self, value):
        self.ambiguous: Target = value
def method_family():
    class LocalTarget:
        pass
    class LocalHolder:
        def __init__(self, value):
            self.payload: LocalTarget = value
    return LocalTarget, LocalHolder
"#;
    let facts = export(source);
    assert!(
        facts.diagnostics.iter().all(
            |diagnostic| diagnostic.severity != DiagnosticSeverity::Error || diagnostic.suppressed
        )
    );
    let explicit = field(&facts, "Holder", "explicit");
    assert_eq!(explicit.annotation_origin, AnnotationOrigin::Explicit);
    let declaration = explicit
        .annotation_definition
        .as_ref()
        .expect("method annotated assignment");
    assert_eq!(
        &source[declaration.source_range.start as usize..declaration.source_range.end as usize],
        "self.explicit: Target = value"
    );
    assert_eq!(field_bindings(&facts, explicit).len(), 1);
    let inferred = field(&facts, "Holder", "inferred");
    assert_eq!(inferred.annotation_origin, AnnotationOrigin::Inferred);
    assert!(inferred.annotation_definition.is_none());
    let ambiguous = field(&facts, "Holder", "ambiguous");
    assert_eq!(ambiguous.annotation_origin, AnnotationOrigin::Explicit);
    assert!(
        ambiguous.annotation_definition.is_none(),
        "multiple declarations are not replaced by a guessed first definition"
    );
    let local = field(&facts, "method_family.<locals>.LocalHolder", "payload");
    let bindings = field_bindings(&facts, local);
    assert_eq!(bindings.len(), 1);
    assert_eq!(
        bindings[0].binding_scope,
        function(&facts, "method_family").identity
    );
    assert_eq!(
        bindings[0].binding,
        class(&facts, "method_family.<locals>.LocalTarget").identity
    );
    // This source field has no native provider/closure operand. Its signed
    // source plan is not an invented runtime capture or admission permission.
    assert!(
        function(&facts, "method_family.<locals>.LocalHolder.__init__")
            .signature
            .parameters
            .iter()
            .all(|parameter| parameter.annotation_origin != AnnotationOrigin::Explicit)
    );
}

#[test]
fn soac_nominal_field_bindings_do_not_publish_partial_normalized_unions() {
    let source = r#"from __future__ import strict
def factory(flag: bool):
    class Target:
        pass
    if flag:
        Alias = Target
    else:
        Alias = Target
    class Holder:
        value: Target | Alias
    def accept(value: Target | Alias) -> Target:
        return value
    return Holder, accept
"#;
    let facts = export(source);
    assert!(
        facts.diagnostics.iter().all(
            |diagnostic| diagnostic.severity != DiagnosticSeverity::Error || diagnostic.suppressed
        )
    );
    let field = field(&facts, "factory.<locals>.Holder", "value");
    assert!(matches!(field.value_type, StaticType::NominalClass(_)));
    assert!(
        field_bindings(&facts, field).is_empty(),
        "one unresolved union alias cannot be dropped after equal class references normalize"
    );
    let function = function(&facts, "factory.<locals>.accept");
    assert!(matches!(
        function.signature.parameters[0].value_type,
        StaticType::NominalClass(_)
    ));
    let bindings: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|binding| function_owns_binding(binding, function))
        .collect();
    assert_eq!(
        bindings.len(),
        1,
        "the independently resolved return remains complete"
    );
    assert!(matches!(
        bindings[0].owner.as_function(),
        Some((_, AnnotationTarget::Return))
    ));
}

#[test]
fn soac_nominal_field_bindings_do_not_require_builtin_arms_or_annotated_metadata() {
    let source = r#"from __future__ import strict
import builtins
from typing import Annotated as Metadata, Final as Frozen
class Target:
    pass
class Optional:
    pass
class Holder:
    number: Target | int
    text: Target | builtins.str
    floating: Target | float
    absent: Target | None
    type_objects: Target | type[Target]
    mixed: Target | int | builtins.str | float | None
    metadata: Metadata[Target, Optional]
    final: Frozen[Target] = Target()
    namesake: Optional | Target
def accept(value: Metadata[Target | int | builtins.str | float | None, Optional]):
    return value
"#;
    let facts = export(source);
    assert!(
        facts.diagnostics.iter().all(
            |diagnostic| diagnostic.severity != DiagnosticSeverity::Error || diagnostic.suppressed
        )
    );
    for (name, count) in [
        ("number", 1),
        ("text", 1),
        ("floating", 1),
        ("absent", 1),
        ("type_objects", 1),
        ("mixed", 1),
        ("metadata", 1),
        ("final", 1),
        ("namesake", 2),
    ] {
        let field = field(&facts, "Holder", name);
        let bindings = field_bindings(&facts, field);
        assert_eq!(bindings.len(), count, "{name}: {:?}", field.value_type);
        if name != "namesake" {
            assert_eq!(bindings[0].name, "Target");
        }
    }
    let bindings: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|binding| function_owns_binding(binding, function(&facts, "accept")))
        .collect();
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].name, "Target");
}

#[test]
fn soac_nominal_field_bindings_keep_external_declarations_and_invalidate_with_source() {
    let base_source = "from __future__ import strict\nfrom dataclasses import dataclass\nclass Target: pass\n@dataclass\nclass Base:\n    inherited: Target\n";
    let main_source = "from __future__ import strict\nfrom dataclasses import dataclass\nfrom base import Base, Target\n@dataclass\nclass Child(Base):\n    own: Target\n";
    let system = TestSystem::default();
    system
        .memory_file_system()
        .write_files_all([
            (
                "/project/ty.toml",
                "[environment]\npython-version = '3.15'\n",
            ),
            ("/project/main.py", main_source),
            ("/project/base.py", base_source),
        ])
        .unwrap();
    let metadata =
        ProjectMetadata::discover(ruff_db::system::SystemPath::new("/project"), &system).unwrap();
    let mut db = ProjectDatabase::fallible_with_analysis_dialect(
        metadata,
        system.clone(),
        AnalysisDialect::SoacStrictV1,
    )
    .unwrap();
    let facts = export_from(&db);
    assert!(
        facts.diagnostics.iter().all(
            |diagnostic| diagnostic.severity != DiagnosticSeverity::Error || diagnostic.suppressed
        )
    );
    let base_file = system_path_to_file(&db, "/project/base.py").unwrap();
    let base = export_soac_module(&db, base_file, "base", ResolvedStrictPolicy::default())
        .unwrap()
        .facts;
    let inherited = field(&facts, "Child", "inherited")
        .annotation_reference()
        .unwrap();
    assert_eq!(
        Some(inherited.clone()),
        field(&base, "Base", "inherited").annotation_reference()
    );
    assert_eq!(inherited.annotation_definition.module, base.module);
    assert_eq!(
        inherited.declaring_class.source_digest,
        Fingerprint::digest(base_source)
    );
    assert_eq!(
        field_bindings(&facts, field(&facts, "Child", "inherited")).len(),
        0
    );
    assert_eq!(
        field_bindings(&base, field(&base, "Base", "inherited")).len(),
        1
    );
    let own = field_bindings(&facts, field(&facts, "Child", "own"));
    assert_eq!(own.len(), 1);
    assert_eq!(own[0].binding.module, facts.module);
    assert_eq!(own[0].class.definition.module, base.module);
    let changed_source = format!("{base_source}# changed declaring module\n");
    system
        .memory_file_system()
        .write_file_all("/project/base.py", &changed_source)
        .unwrap();
    db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
        "/project/base.py".into(),
    )]);
    let changed = export_from(&db);
    assert_eq!(changed.module, facts.module);
    let changed_inherited = field(&changed, "Child", "inherited")
        .annotation_reference()
        .unwrap();
    assert_ne!(changed_inherited, inherited);
    assert_eq!(
        changed_inherited.annotation_definition.source_range,
        inherited.annotation_definition.source_range
    );
    assert_eq!(
        changed_inherited.declaring_class.source_digest,
        Fingerprint::digest(&changed_source)
    );
    system
        .memory_file_system()
        .write_file_all("/project/base.py", base_source)
        .unwrap();
    db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
        "/project/base.py".into(),
    )]);
    assert_eq!(export_from(&db), facts);
}

#[test]
fn soac_implicit_class_cell_reaches_nested_lexical_scopes() {
    let source = r#"from __future__ import strict
def exercise():
    class C:
        def method(self):
            def nested():
                return __class__
            return nested()
    return C().method(), C
class ModuleClass:
    def method(self):
        callbacks = [lambda: __class__ for _ in range(2)]
        class Inner:
            enclosing = __class__
        return callbacks, Inner
    nested_lambda = lambda: (lambda: __class__)
    nested_generator = (lambda: __class__ for _ in range(2))
"#;
    let facts = export(source);
    assert_eq!(
        facts,
        export_from(&database(source, AnalysisDialect::SoacStrictV1, true))
    );
    assert!(
        !facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error),
        "{:?}",
        facts.diagnostics
    );
    assert_eq!(
        class(&facts, "exercise.<locals>.C").participation,
        ParticipationProposal::Candidate
    );
    let ordinary = source.replace("from __future__ import strict", "# ordinary source");
    let db = database(&ordinary, AnalysisDialect::Python, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    assert!(ty_python_semantic::Db::check_file(&db, file).is_empty());
}

#[test]
fn soac_implicit_class_cell_preserves_explicit_bindings() {
    let source = r#"from __future__ import strict
__class__ = 7
class C:
    def parameter(self, __class__: int):
        def nested() -> int:
            return __class__
        return nested
    def declared(self):
        __class__: int
        def nested() -> int:
            return __class__
        return nested
    def local(self):
        __class__ = 'value'
        def middle():
            nonlocal __class__
            def nested() -> str:
                return __class__
            return nested
        return middle
    def forwarded_global(self):
        global __class__
        def nested() -> int:
            return __class__
        return nested
    def nested_global(self):
        def nested() -> int:
            global __class__
            return __class__
        return nested
"#;
    let facts = export(source);
    assert!(
        !facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error),
        "{:?}",
        facts.diagnostics
    );
}

#[test]
fn soac_implicit_class_cell_does_not_grant_nonlexical_or_unbound_names() {
    for source in [
        "def outside():\n    def nested(): return __class__\n    return nested\nclass C: method = outside\n",
        "class C:\n    value = __class__\n",
        "class C:\n    def method(self, value=__class__): pass\n",
        "class C:\n    values = [__class__ for _ in range(1)]\n",
        "class C:\n    values = (value for value in (__class__,))\n",
        "class C:\n    class Inner:\n        value = __class__\n",
        "class C:\n    def method(self):\n        global __class__\n        def nested(): return __class__\n        return nested\n",
        "class C:\n    def method(self):\n        def nested():\n            result = __class__\n            __class__ = 7\n            return result\n        return nested\n",
    ] {
        let db = database(
            &format!("from __future__ import strict\n{source}"),
            AnalysisDialect::SoacStrictV1,
            false,
        );
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        let facts =
            export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
        assert!(
            facts
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error),
            "invalid implicit class-cell use was accepted: {source}"
        );
    }
}

#[test]
fn soac_nonlocal_class_cell_has_no_namespace_binding() {
    let source = r#"from __future__ import strict
def factory():
    class Model:
        def reader(self):
            def read():
                nonlocal __class__
                return __class__
            return read
        def replace(self, value):
            nonlocal __class__
            __class__ = value
        def erase(self):
            nonlocal __class__
            del __class__
        def direct(self):
            return __class__
    return Model
"#;
    let facts = export(source);
    assert_eq!(
        facts,
        export_from(&database(source, AnalysisDialect::SoacStrictV1, true))
    );
    assert!(
        facts
            .global_bindings
            .iter()
            .all(|binding| binding.name != "__class__")
    );
    let owner = class(&facts, "factory.<locals>.Model");
    assert_eq!(owner.participation, ParticipationProposal::Candidate);
    assert!(
        owner
            .class_members
            .iter()
            .all(|member| member.name != "__class__")
    );
    assert!(
        owner
            .instance_fields
            .iter()
            .all(|field| field.name != "__class__")
    );
    for name in ["reader", "replace", "erase", "direct"] {
        let method = function(&facts, &format!("factory.<locals>.Model.{name}"));
        assert_eq!(
            method.signature.return_annotation_origin,
            AnnotationOrigin::Absent
        );
    }
    let ordinary = source.replace("from __future__ import strict", "# ordinary source");
    let db = database(&ordinary, AnalysisDialect::Python, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    assert!(ty_python_semantic::Db::check_file(&db, file).is_empty());
}

#[test]
fn soac_nonlocal_class_cell_does_not_write_an_outer_namesake() {
    let source = r#"from __future__ import strict
def outer() -> int:
    __class__: int = 7
    class Model:
        def replace(self):
            nonlocal __class__
            __class__ = "changed"
        def indirect(self):
            def replace():
                nonlocal __class__
                __class__ = b"nested"
            return replace
    return __class__
"#;
    let facts = export(source);
    assert!(
        facts
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity != DiagnosticSeverity::Error)
    );
    let invalid = source.replace(
        "            def replace():",
        "            __class__: int = 1\n            def replace():",
    );
    let db = database(&invalid, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let program_file = ty_python_semantic::Db::program_file(&db, file);
    let index = ty_python_core::semantic_index(&db, program_file);
    let parsed = ruff_db::parsed::parsed_module(&db, program_file.python_file(&db)).load(&db);
    let local_owner = index
        .scope_ids()
        .find(|scope| scope.name(&db, &parsed) == "indirect")
        .unwrap()
        .file_scope_id(&db);
    let nested = index
        .scope_ids()
        .find(|scope| index.scope(scope.file_scope_id(&db)).parent() == Some(local_owner))
        .unwrap()
        .file_scope_id(&db);
    assert!(index.implicit_class_cell(local_owner).is_none());
    assert!(index.implicit_class_cell(nested).is_none());
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(
        facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error),
        "{invalid}\n{:?}",
        facts.diagnostics
    );
}

#[test]
fn soac_eager_nested_class_cell_has_distinct_forwarded_and_method_owners() {
    let source = r#"from __future__ import strict
__class__ = 100
def factory():
    class Outer:
        class Inner:
            nonlocal __class__
            __class__ = "construction"
            saved: str = __class__
            def own_class(self):
                return __class__
            def replace(self, value):
                nonlocal __class__
                __class__ = value
        def own_class(self):
            return __class__
        def replace(self, value):
            nonlocal __class__
            __class__ = value
    return Outer
"#;
    let db = database(source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let program_file = ty_python_semantic::Db::program_file(&db, file);
    let parsed = ruff_db::parsed::parsed_module(&db, program_file.python_file(&db)).load(&db);
    let index = ty_python_core::semantic_index(&db, program_file);
    let class_scope = |name| {
        index
            .scope_ids()
            .find(|scope| {
                scope.node(&db).scope_kind().is_class() && scope.name(&db, &parsed) == name
            })
            .unwrap()
            .file_scope_id(&db)
    };
    let outer = class_scope("Outer");
    let inner = class_scope("Inner");
    let method_scope = |owner, name| {
        index
            .scope_ids()
            .find(|scope| {
                index.scope(scope.file_scope_id(&db)).parent() == Some(owner)
                    && scope.name(&db, &parsed) == name
            })
            .unwrap()
            .file_scope_id(&db)
    };
    let outer_cell = index
        .implicit_class_cell(method_scope(outer, "own_class"))
        .unwrap();
    let inner_cell = index
        .implicit_class_cell(method_scope(inner, "own_class"))
        .unwrap();
    assert_ne!(outer_cell, inner_cell);
    assert_eq!(index.implicit_class_cell(inner), Some(outer_cell));
    assert!(
        index
            .implicit_class_cell_write_scopes(outer_cell)
            .contains(&inner)
    );
    assert!(
        !index
            .implicit_class_cell_write_scopes(inner_cell)
            .contains(&inner)
    );
    assert!(
        index
            .implicit_class_cell_write_scopes(inner_cell)
            .contains(&method_scope(inner, "replace"))
    );
    assert!(
        !index
            .implicit_class_cell_write_scopes(outer_cell)
            .contains(&method_scope(inner, "replace"))
    );

    let facts = export_from(&db);
    for class_name in ["factory.<locals>.Outer", "factory.<locals>.Outer.Inner"] {
        assert!(
            class(&facts, class_name)
                .class_members
                .iter()
                .all(|member| member.name != "__class__"),
            "{class_name}"
        );
    }
    let global = facts
        .global_bindings
        .iter()
        .find(|binding| binding.name == "__class__")
        .unwrap();
    assert_eq!(
        global.value_type,
        StaticType::Literal(LiteralValue::Int("100".into()))
    );
    assert_eq!(global.mutability, GlobalMutability::FinalAfterSeal);
    let ordinary = source.replace("from __future__ import strict", "# ordinary source");
    let ordinary = database(&ordinary, AnalysisDialect::Python, false);
    let file = system_path_to_file(&ordinary, "/project/main.py").unwrap();
    assert!(ty_python_semantic::Db::check_file(&ordinary, file).is_empty());
}

#[test]
fn soac_eager_nested_class_cell_does_not_grant_a_completed_value() {
    let source = r#"from __future__ import strict
__class__ = 100
class Outer:
    class Inner:
        nonlocal __class__
        before = __class__
"#;
    let db = database(source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(
        facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
    );
}

#[test]
fn soac_eager_nested_class_cell_keeps_explicit_owner_and_namespace_boundaries() {
    let source = r#"from __future__ import strict
global_name = 1
def factory():
    outer_name = 2
    class Outer:
        __class__ = "namespace"
        class Inner:
            nonlocal __class__, outer_name
            global global_name
            __class__ = "construction"
            outer_name = 3
            global_name = 4
            saved = __class__
        def own_class(self):
            return __class__
    return Outer
"#;
    let facts = export(source);
    let outer = class(&facts, "factory.<locals>.Outer");
    assert!(
        outer
            .class_members
            .iter()
            .any(|member| member.name == "__class__")
    );
    let inner = class(&facts, "factory.<locals>.Outer.Inner");
    for name in ["__class__", "outer_name", "global_name"] {
        assert!(
            inner.class_members.iter().all(|member| member.name != name),
            "{name}"
        );
    }
    assert!(
        inner
            .class_members
            .iter()
            .any(|member| member.name == "saved")
    );

    for invalid in [
        "class Alone:\n    nonlocal __class__\n",
        "__class__ = 100\nclass Alone:\n    nonlocal __class__\n",
        "class Outer:\n    def method(self):\n        global __class__\n        class Inner:\n            nonlocal __class__\n",
    ] {
        let db = database(invalid, AnalysisDialect::Python, false);
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        assert!(
            !ty_python_semantic::Db::check_file(&db, file).is_empty(),
            "{invalid}"
        );
    }
}

#[test]
fn soac_implicit_class_cell_preserves_a_generic_methods_type_parameter_owner() {
    let source = "class Model:\n    def method[__class__](self):\n        return __class__\n";
    let db = database(source, AnalysisDialect::Python, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let program_file = ty_python_semantic::Db::program_file(&db, file);
    let index = ty_python_core::semantic_index(&db, program_file);
    let scope = index
        .scope_ids()
        .find(|scope| scope.node(&db).scope_kind() == ty_python_core::scope::ScopeKind::Function)
        .unwrap()
        .file_scope_id(&db);
    assert!(index.class_definition_of_method(scope).is_some());
    assert!(index.implicit_class_cell(scope).is_none());
    assert!(ty_python_semantic::Db::check_file(&db, file).is_empty());
}

#[test]
fn soac_lambda_identities_follow_lexical_definition_scopes() {
    let source = r#"from __future__ import strict
module_list = [lambda: module_index for module_index in range(2)]
module_set = {lambda: set_index for set_index in range(2)}
module_dict = {dict_index: lambda: dict_index for dict_index in range(2)}
module_generator = (lambda: generator_index for generator_index in range(2))
generator_input = (item for item in (lambda: range(2))())
nested = lambda: (lambda: "nested")
class ModuleClass:
    values = [lambda: module_class_index for module_class_index in range(2)]
def factory():
    local_list = [lambda: local_index for local_index in range(2)]
    class Owner:
        values = [lambda: class_index for class_index in range(2)]
        generated = (lambda: class_generator for class_generator in range(2))
        nested = lambda: (lambda: "class_nested")
    return Owner
"#;
    let facts = export(source);
    let expected = [
        ("lambda: module_index", "<lambda>"),
        ("lambda: set_index", "<lambda>"),
        ("lambda: dict_index", "<lambda>"),
        ("lambda: generator_index", "<lambda>"),
        ("lambda: range(2)", "<lambda>"),
        ("lambda: (lambda: \"nested\")", "<lambda>"),
        ("lambda: \"nested\"", "<lambda>.<lambda>"),
        ("lambda: module_class_index", "ModuleClass.<lambda>"),
        ("lambda: local_index", "factory.<locals>.<lambda>"),
        ("lambda: class_index", "factory.<locals>.Owner.<lambda>"),
        ("lambda: class_generator", "factory.<locals>.Owner.<lambda>"),
        (
            "lambda: (lambda: \"class_nested\")",
            "factory.<locals>.Owner.<lambda>",
        ),
        (
            "lambda: \"class_nested\"",
            "factory.<locals>.Owner.<lambda>.<lambda>",
        ),
    ];
    assert_eq!(
        facts
            .functions
            .iter()
            .filter(|function| { function.identity.definition_kind == DefinitionKind::Lambda })
            .count(),
        expected.len()
    );
    for (expression, qualname) in expected {
        let start = source.find(expression).unwrap();
        let range = SourceRange::new(start as u32, (start + expression.len()) as u32);
        let function = facts
            .functions
            .iter()
            .find(|function| function.identity.source_range == range)
            .unwrap();
        assert_eq!(function.identity.definition_kind, DefinitionKind::Lambda);
        assert_eq!(function.identity.lexical_qualname, qualname, "{expression}");
        assert_eq!(function.identity.module, facts.module);
    }
    assert_eq!(
        facts,
        export_from(&database(source, AnalysisDialect::SoacStrictV1, true))
    );
}

#[test]
fn soac_lambda_default_expressions_keep_the_enclosing_scope() {
    let source = r#"from __future__ import strict
module_value = lambda fn=(lambda: "module_default"): fn()
class Owner:
    value = lambda fn=(lambda: "class_default"): fn()
def factory():
    return lambda fn=(lambda: "function_default"): (lambda: fn())
"#;
    let facts = export(source);
    for (expression, qualname) in [
        ("lambda: \"module_default\"", "<lambda>"),
        ("lambda: \"class_default\"", "Owner.<lambda>"),
        ("lambda: \"function_default\"", "factory.<locals>.<lambda>"),
        ("lambda: fn()", "factory.<locals>.<lambda>.<lambda>"),
    ] {
        let start = source.find(expression).unwrap();
        let range = SourceRange::new(start as u32, (start + expression.len()) as u32);
        let function = facts
            .functions
            .iter()
            .find(|function| function.identity.source_range == range)
            .unwrap();
        assert_eq!(function.identity.lexical_qualname, qualname, "{expression}");
    }
    let nested_call = facts
        .call_sites
        .iter()
        .find(|call| {
            let range = &call.identity.expression_range;
            &source[range.start as usize..range.end as usize] == "fn()"
                && call.identity.enclosing_function.lexical_qualname
                    == "factory.<locals>.<lambda>.<lambda>"
        })
        .unwrap();
    assert!(
        facts
            .functions
            .iter()
            .any(|function| { function.identity == nested_call.identity.enclosing_function })
    );
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
            .filter(|leaf| function_owns_binding(leaf, function))
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
            .filter(|leaf| function_owns_binding(leaf, function))
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
        .filter(|binding| function_owns_binding(binding, combine))
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
        .find(|binding| parameter_owns_binding(binding, 1))
        .unwrap();
    assert_eq!(alias.name, "Alias");
    assert_eq!(alias.binding.module, facts.module);
    assert_eq!(alias.binding.definition_kind, DefinitionKind::Assignment);
    assert_eq!(alias.class.definition.module.module_name, "external");
    assert_eq!(alias.class.definition.lexical_qualname, "Foreign");
    let local_alias = bindings
        .iter()
        .find(|binding| parameter_owns_binding(binding, 2))
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
            function_owns_binding(binding, duplicate) && parameter_owns_binding(binding, 0)
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
fn soac_nominal_plain_imports_keep_local_binding_and_foreign_class_identities() {
    let source = r#"from __future__ import strict
from typing import Optional, Union
from external import Foreign
from external import Foreign as Alias
def direct(owner: Foreign) -> Foreign:
    return owner
def quoted(owner: "Foreign") -> "Foreign":
    return owner
def combined(owner: "Foreign | Alias", extra: Optional[Foreign]) -> Union[Foreign, Alias]:
    return owner
"#;
    let facts = export(source);
    for (name, count) in [("direct", 2), ("quoted", 2), ("combined", 5)] {
        let function = function(&facts, name);
        let leaves: Vec<_> = facts
            .nominal_bindings
            .iter()
            .filter(|leaf| function_owns_binding(leaf, function))
            .collect();
        assert_eq!(leaves.len(), count, "{name}");
        for leaf in leaves {
            assert_eq!(leaf.binding_scope, facts.module_body_identity());
            assert_eq!(leaf.binding.module, facts.module);
            assert_eq!(leaf.binding.definition_kind, DefinitionKind::Assignment);
            assert_eq!(leaf.class.definition.module.module_name, "external");
            assert_eq!(leaf.class.definition.lexical_qualname, "Foreign");
            assert_ne!(leaf.binding, leaf.class.definition);
            let global = facts
                .global_bindings
                .iter()
                .find(|binding| binding.name == leaf.name)
                .unwrap();
            assert_eq!(global.definition.as_ref(), Some(&leaf.binding));
            let import_text = match leaf.name.as_str() {
                "Foreign" => "Foreign",
                "Alias" => "Foreign as Alias",
                name => panic!("unexpected imported leaf {name}"),
            };
            let import_start = source
                .find(&format!("from external import {import_text}\n"))
                .unwrap()
                + "from external import ".len();
            assert_eq!(
                leaf.binding.source_range,
                SourceRange::new(
                    import_start as u32,
                    (import_start + import_text.len()) as u32
                )
            );
            let dependency = facts
                .consumed_dependencies
                .iter()
                .find(|dependency| dependency.module == leaf.class.definition.module)
                .unwrap();
            assert_eq!(leaf.class.source_digest, dependency.source_digest);
        }
    }
    assert_eq!(
        facts,
        export_from(&database(source, AnalysisDialect::SoacStrictV1, true))
    );
}

#[test]
fn soac_nominal_plain_imports_retain_exact_class_and_function_scopes() {
    let source = r#"from __future__ import strict
class Container:
    from external import Foreign
    def method(self, value: Foreign) -> Foreign:
        return value
def factory():
    from external import Foreign
    def inner(value: "Foreign") -> "Foreign":
        return value
    return inner
"#;
    let facts = export(source);
    for (name, scope) in [
        ("Container.method", &class(&facts, "Container").identity),
        (
            "factory.<locals>.inner",
            &function(&facts, "factory").identity,
        ),
    ] {
        let function = function(&facts, name);
        let leaves: Vec<_> = facts
            .nominal_bindings
            .iter()
            .filter(|leaf| function_owns_binding(leaf, function))
            .collect();
        assert_eq!(leaves.len(), 2, "{name}");
        for leaf in leaves {
            assert_eq!(&leaf.binding_scope, scope);
            assert_eq!(leaf.binding.module, facts.module);
            assert_eq!(leaf.binding.definition_kind, DefinitionKind::Assignment);
            assert_eq!(leaf.class.definition.module.module_name, "external");
            assert_eq!(
                &source[leaf.binding.source_range.start as usize
                    ..leaf.binding.source_range.end as usize],
                "Foreign"
            );
        }
    }
}

#[test]
fn soac_nominal_imports_do_not_guess_ambiguous_star_attribute_or_shadowed_bindings() {
    let source = r#"from __future__ import strict
from external import Foreign
import external
def attribute(value: external.Foreign) -> external.Foreign:
    return value
def ambiguous_factory(flag: bool):
    if flag:
        from external import Foreign
    else:
        from external import Foreign
    def inner(value: Foreign) -> Foreign:
        return value
    return inner
def shadowed_factory():
    class Foreign:
        pass
    def inner(value: Foreign) -> Foreign:
        return value
    return inner
"#;
    let facts = export(source);
    for name in ["attribute", "ambiguous_factory.<locals>.inner"] {
        let function = function(&facts, name);
        assert!(matches!(
            function.signature.parameters[0].value_type,
            StaticType::NominalClass(_)
        ));
        assert!(
            facts
                .nominal_bindings
                .iter()
                .all(|leaf| !function_owns_binding(leaf, function))
        );
    }
    let shadowed = function(&facts, "shadowed_factory.<locals>.inner");
    let local = class(&facts, "shadowed_factory.<locals>.Foreign");
    let leaves: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|leaf| function_owns_binding(leaf, shadowed))
        .collect();
    assert_eq!(leaves.len(), 2);
    assert!(leaves.iter().all(|leaf| {
        leaf.binding == local.identity
            && leaf.class.definition == local.identity
            && leaf.binding_scope == function(&facts, "shadowed_factory").identity
    }));

    let star = export(
        "from __future__ import strict\nfrom external import *\ndef direct(value: Foreign) -> Foreign:\n    return value\n",
    );
    assert!(matches!(
        function(&star, "direct").signature.parameters[0].value_type,
        StaticType::NominalClass(_)
    ));
    assert!(star.nominal_bindings.is_empty());
}

#[test]
fn soac_nominal_import_mode_does_not_change_ordinary_ide_alias_resolution() {
    use ruff_python_ast::{Expr, Stmt};
    use ty_python_core::definition::DefinitionKind as SemanticDefinitionKind;
    use ty_python_semantic::{ImportAliasResolution, SemanticModel, definitions_for_name};

    let source =
        "from external import Foreign\nfrom external import Foreign as Alias\nForeign\nAlias\n";
    let db = database(source, AnalysisDialect::Python, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let program_file = ty_python_semantic::Db::program_file(&db, file);
    let model = SemanticModel::new(&db, program_file);
    let parsed = ruff_db::parsed::parsed_module(&db, program_file.python_file(&db)).load(&db);
    let mut names = 0;
    for statement in parsed.suite() {
        let Stmt::Expr(statement) = statement else {
            continue;
        };
        let Expr::Name(name) = statement.value.as_ref() else {
            panic!("fixture expression must be a name");
        };
        names += 1;
        for mode in [
            ImportAliasResolution::ResolveAliases,
            ImportAliasResolution::PreserveAliases,
            ImportAliasResolution::PreserveImports,
        ] {
            let definitions = definitions_for_name(&model, name.id.as_str(), name.into(), mode);
            assert_eq!(definitions.len(), 1);
            let definition = definitions[0].definition().unwrap();
            let local = mode == ImportAliasResolution::PreserveImports
                || (name.id == "Alias" && mode == ImportAliasResolution::PreserveAliases);
            assert_eq!(definition.program_file(&db) == program_file, local);
            if local {
                assert!(matches!(
                    definition.kind(&db),
                    SemanticDefinitionKind::ImportFrom(_)
                ));
            } else {
                assert!(matches!(
                    definition.kind(&db),
                    SemanticDefinitionKind::Class(_)
                ));
            }
        }
    }
    assert_eq!(names, 2);
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
            function_owns_binding(binding, method) && parameter_owns_binding(binding, 1)
        })
        .unwrap();
    assert_eq!(local.binding_scope, class(&facts, "Container").identity);
    assert_eq!(local.binding.definition_kind, DefinitionKind::Assignment);
    let outer = function(&facts, "outer");
    let inner = function(&facts, "outer.<locals>.inner");
    let inner_bindings: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|binding| function_owns_binding(binding, inner))
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
                .all(|binding| !function_owns_binding(binding, function(&facts, name)))
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
        .filter(|leaf| function_owns_binding(leaf, direct))
        .collect();
    assert_eq!(direct_leaves.len(), 2);
    assert!(direct_leaves.iter().all(|leaf| {
        leaf.binding == local.identity && leaf.binding_scope == function(&facts, "factory").identity
    }));
    let alias_leaves: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|leaf| function_owns_binding(leaf, alias))
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
        .filter(|leaf| function_owns_binding(leaf, two))
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
        .filter(|leaf| function_owns_binding(leaf, either))
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
fn soac_dataclass_init_receiver_follows_all_semantic_field_names() {
    for (body, parameters) in [
        ("self: int", vec!["__dataclass_self__", "self", "payload"]),
        (
            "self: InitVar[Target]",
            vec!["__dataclass_self__", "self", "payload"],
        ),
        (
            "self: int = field(init=False)",
            vec!["__dataclass_self__", "payload"],
        ),
        (
            "self: ClassVar[int] = 0",
            vec!["__dataclass_self__", "payload"],
        ),
        ("self = 0", vec!["self", "payload"]),
        ("def self(instance): pass", vec!["self", "payload"]),
        ("self: KW_ONLY", vec!["self", "payload"]),
        (
            "__dataclass_self__: int",
            vec!["self", "__dataclass_self__", "payload"],
        ),
    ] {
        let source = format!(
            "from __future__ import strict\nfrom dataclasses import dataclass, field, InitVar, KW_ONLY\nfrom typing import ClassVar\nclass Target: pass\n@dataclass\nclass Record:\n    {body}\n    payload: int\n"
        );
        let db = database(&source, AnalysisDialect::SoacStrictV1, false);
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        let facts =
            export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
        assert!(
            facts.diagnostics.iter().all(|diagnostic| {
                diagnostic.severity != DiagnosticSeverity::Error || diagnostic.suppressed
            }),
            "{body}: {:?}",
            facts.diagnostics
        );
        let record = class(&facts, "Record");
        let init = record
            .methods
            .iter()
            .find(|method| method.name == "__init__")
            .unwrap();
        assert_eq!(
            init.signature
                .parameters
                .iter()
                .map(|parameter| parameter.name.as_str())
                .collect::<Vec<_>>(),
            parameters,
            "{body}"
        );
        assert_eq!(
            init.signature.parameters[0].annotation_origin,
            AnnotationOrigin::Inferred
        );
        assert!(
            init.signature
                .parameters
                .iter()
                .skip(1)
                .all(|parameter| parameter.annotation_origin == AnnotationOrigin::Explicit)
        );
        assert_eq!(
            init.signature.return_annotation_origin,
            AnnotationOrigin::Inferred
        );
        assert!(matches!(init.signature.return_type, StaticType::None));
        if body == "self: InitVar[Target]" {
            let field = field(&facts, "Record", "self");
            assert_eq!(field.field_kind, FieldKind::InitOnly);
            assert_eq!(init.signature.parameters[1].value_type, field.value_type);
            assert_eq!(field_bindings(&facts, field).len(), 1);
        }
        // Other generated methods keep their own stdlib receiver names.
        for name in ["__repr__", "__eq__"] {
            if let Some(method) = record.methods.iter().find(|method| method.name == name) {
                assert_eq!(method.signature.parameters[0].name, "self", "{name}");
            }
        }
        let replace = record
            .methods
            .iter()
            .find(|method| method.name == "__replace__")
            .unwrap();
        assert_eq!(
            replace.signature.parameters[0].kind,
            ParameterKind::PositionalOnly
        );
        assert_eq!(
            replace.signature.parameters[0].annotation_origin,
            AnnotationOrigin::Inferred
        );
        export_from(&db);
    }
}

#[test]
fn soac_dataclass_init_receiver_includes_inherited_fields_not_ordinary_attributes() {
    for (base, expected_receiver, expected_field) in [
        (
            "@dataclass\nclass Base:\n    self: int",
            "__dataclass_self__",
            true,
        ),
        (
            "@dataclass\nclass Base:\n    self: int = field(init=False)",
            "__dataclass_self__",
            false,
        ),
        (
            "@dataclass\nclass Base:\n    self: ClassVar[int] = 0",
            "__dataclass_self__",
            false,
        ),
        ("@dataclass\nclass Base:\n    self: KW_ONLY", "self", false),
        ("class Base:\n    self: int", "self", false),
    ] {
        let source = format!(
            "from __future__ import strict\nfrom dataclasses import dataclass, field, KW_ONLY\nfrom typing import ClassVar\n{base}\nclass Middle(Base): pass\n@dataclass\nclass Record(Middle):\n    payload: int\n"
        );
        let facts = export(&source);
        let record = class(&facts, "Record");
        let init = record
            .methods
            .iter()
            .find(|method| method.name == "__init__")
            .unwrap();
        assert_eq!(
            init.signature.parameters[0].name, expected_receiver,
            "{base}"
        );
        assert_eq!(
            init.signature
                .parameters
                .iter()
                .skip(1)
                .any(|parameter| parameter.name == "self"),
            expected_field,
            "{base}"
        );
    }
}

#[test]
fn soac_dataclass_init_receiver_uses_stdlib_provenance_not_shared_field_specifiers() {
    let facts = export(
        r#"from __future__ import strict
from dataclasses import dataclass as native_dataclass, field
from typing import ClassVar, dataclass_transform
@dataclass_transform(field_specifiers=(field,))
def dataclass[T](cls: type[T]) -> type[T]:
    return cls
@dataclass
class Custom:
    self: ClassVar[int] = 0
configured = native_dataclass(kw_only=True)
@configured
class Native:
    self: int
"#,
    );
    for (name, init_receiver, replace_kind) in [
        ("Custom", "self", ParameterKind::PositionalOrKeyword),
        (
            "Native",
            "__dataclass_self__",
            ParameterKind::PositionalOnly,
        ),
    ] {
        let record = class(&facts, name);
        let init = record
            .methods
            .iter()
            .find(|method| method.name == "__init__")
            .unwrap();
        assert_eq!(init.signature.parameters[0].name, init_receiver);
        let replace = record
            .methods
            .iter()
            .find(|method| method.name == "__replace__")
            .unwrap();
        assert_eq!(replace.signature.parameters[0].kind, replace_kind);
    }
}

#[test]
fn soac_dataclass_init_receiver_preserves_real_name_conflicts_and_unnamed_labels() {
    let facts = export(
        "from __future__ import strict\nfrom dataclasses import dataclass\n@dataclass\nclass Record:\n    self: int\n    arg0: int\n    arg0_: int\n",
    );
    let record = class(&facts, "Record");
    let replace = record
        .methods
        .iter()
        .find(|method| method.name == "__replace__")
        .unwrap();
    assert_eq!(
        replace
            .signature
            .parameters
            .iter()
            .map(|parameter| parameter.name.as_str())
            .collect::<Vec<_>>(),
        ["arg0__", "self", "arg0", "arg0_"]
    );
    assert_eq!(
        replace.signature.parameters[0].kind,
        ParameterKind::PositionalOnly
    );
    assert!(
        replace
            .signature
            .parameters
            .iter()
            .skip(1)
            .all(|parameter| parameter.kind == ParameterKind::KeywordOnly
                && parameter.annotation_origin == AnnotationOrigin::Explicit)
    );

    // CPython rejects these two actual field names because its chosen receiver
    // also occurs in the constructor fields. Do not invent another native name.
    let db = database(
        "from __future__ import strict\nfrom dataclasses import dataclass\n@dataclass\nclass Conflict:\n    self: int\n    __dataclass_self__: int\n",
        AnalysisDialect::SoacStrictV1,
        false,
    );
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    let init = class(&facts, "Conflict")
        .methods
        .iter()
        .find(|method| method.name == "__init__")
        .unwrap();
    assert_eq!(
        init.signature
            .parameters
            .iter()
            .map(|parameter| parameter.name.as_str())
            .collect::<Vec<_>>(),
        ["__dataclass_self__", "self", "__dataclass_self__"]
    );
}

#[test]
fn soac_dataclass_comparison_catalog_uses_generated_signatures_and_own_options() {
    let facts = export(
        r#"from __future__ import strict
from dataclasses import dataclass
@dataclass
class Base:
    value: int = 1
@dataclass
class Child(Base):
    extra: int = 2
class Inherited(Base):
    pass
@dataclass(repr=False, eq=False)
class Disabled(Base):
    pass
@dataclass(repr=False)
class EqualityOnly:
    value: int = 1
@dataclass(eq=False)
class ReprOnly:
    value: int = 1
"#,
    );
    for (class_name, repr, eq) in [
        ("Base", true, true),
        ("Child", true, true),
        ("Inherited", false, false),
        ("Disabled", false, false),
        ("EqualityOnly", false, true),
        ("ReprOnly", true, false),
    ] {
        let record = class(&facts, class_name);
        for (name, generated, parameter_names, return_type) in [
            ("__repr__", repr, &["self"][..], BuiltinType::Str),
            ("__eq__", eq, &["self", "other"][..], BuiltinType::Bool),
        ] {
            let method = record.methods.iter().find(|method| method.name == name);
            assert_eq!(method.is_some(), generated, "{class_name}.{name}");
            assert_eq!(
                record
                    .transform
                    .as_ref()
                    .is_some_and(|transform| transform.generated_methods.contains(name)),
                generated,
                "{class_name}.{name} must be in its own generated catalog only"
            );
            let Some(method) = method else { continue };
            let origin = method.generated.as_ref().unwrap();
            assert_eq!(origin.class.definition, record.identity);
            assert_eq!(origin.name, name);
            assert!(method.implementation.is_none());
            assert_eq!(
                method
                    .signature
                    .parameters
                    .iter()
                    .map(|parameter| parameter.name.as_str())
                    .collect::<Vec<_>>(),
                parameter_names
            );
            for parameter in &method.signature.parameters {
                assert_eq!(parameter.kind, ParameterKind::PositionalOrKeyword);
                assert_eq!(parameter.default, DefaultFact::Missing);
                assert_eq!(parameter.annotation_origin, AnnotationOrigin::Inferred);
            }
            assert_eq!(
                method.signature.return_type,
                StaticType::NominalBuiltin {
                    builtin: return_type,
                    allow_subclasses: true,
                }
            );
            assert_eq!(
                method.signature.return_annotation_origin,
                AnnotationOrigin::Inferred,
                "synthetic return typing is not a source annotation"
            );
            if name == "__eq__" {
                assert_eq!(
                    method.signature.parameters[1].value_type,
                    StaticType::NominalBuiltin {
                        builtin: BuiltinType::Object,
                        allow_subclasses: true,
                    },
                    "dataclass equality accepts foreign objects too"
                );
            }
        }
        assert!(
            !record
                .transform
                .as_ref()
                .is_some_and(|transform| { transform.generated_methods.contains("__ne__") }),
            "dataclasses do not generate __ne__"
        );
    }
}

#[test]
fn soac_dataclass_comparison_catalog_preserves_explicit_and_assigned_overrides() {
    let facts = export(
        r#"from __future__ import strict
from dataclasses import dataclass
@dataclass
class Explicit:
    value: int = 1
    def __repr__(self) -> str:
        return "explicit"
    def __eq__(self, other: object) -> bool:
        return self is other
@dataclass
class Assigned:
    value: int = 1
    __repr__ = lambda self: "assigned"
    __eq__ = lambda self, other: False
"#,
    );
    for class_name in ["Explicit", "Assigned"] {
        let record = class(&facts, class_name);
        let transform = record.transform.as_ref().unwrap();
        for name in ["__repr__", "__eq__"] {
            assert!(!transform.generated_methods.contains(name));
            if class_name == "Explicit" {
                let method = record
                    .methods
                    .iter()
                    .find(|method| method.name == name)
                    .unwrap();
                assert!(method.generated.is_none());
                assert_eq!(
                    method.implementation.as_ref().unwrap().lexical_qualname,
                    format!("{class_name}.{name}")
                );
                assert_eq!(
                    method.signature.return_annotation_origin,
                    AnnotationOrigin::Explicit
                );
            } else {
                assert!(!record.methods.iter().any(|method| method.name == name));
                let member = record
                    .class_members
                    .iter()
                    .find(|member| member.name == name)
                    .unwrap();
                assert!(matches!(member.value_type, StaticType::Callable(_)));
                assert!(member.definition.is_some());
            }
        }
    }
}

#[test]
fn soac_dataclass_comparison_catalog_distinguishes_declarations_from_live_bindings() {
    let declared = export(
        r#"from __future__ import strict
from dataclasses import dataclass
from typing import Callable, ClassVar
@dataclass
class DeclaredOnly:
    __repr__: ClassVar[Callable[[object], str]]
    __eq__: ClassVar[Callable[[object, object], bool]]
"#,
    );
    let deleted_source = r#"from __future__ import strict
from dataclasses import dataclass
@dataclass
class Deleted:
    def __repr__(self) -> str:
        return "removed"
    def __eq__(self, other: object) -> bool:
        return False
    del __repr__, __eq__
"#;
    let db = database(deleted_source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let diagnostics = ty_python_semantic::Db::check_file(&db, file);
    // TODO: The preexisting override checker combines bound and unbound method
    // views after `del`, rejecting this native-valid source. The raw prediction
    // still describes generation, but this is deliberately not an admission test.
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .id()
            .as_lint()
            .is_some_and(|name| name.as_str() == "invalid-method-override")
    }));
    let deleted =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(
        deleted
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
    );
    for (facts, class_name) in [(&declared, "DeclaredOnly"), (&deleted, "Deleted")] {
        let record = class(facts, class_name);
        for name in ["__repr__", "__eq__"] {
            assert!(
                record
                    .transform
                    .as_ref()
                    .unwrap()
                    .generated_methods
                    .contains(name),
                "{class_name}.{name}: methods={:?}, class_members={:?}",
                record.methods,
                record.class_members
            );
            assert!(
                record
                    .methods
                    .iter()
                    .find(|method| method.name == name)
                    .unwrap()
                    .generated
                    .is_some()
            );
        }
    }

    let db = database(
        "from __future__ import strict\nfrom dataclasses import dataclass\n@dataclass\nclass NonCallable:\n    __repr__ = 42\n    __eq__ = None\nNonCallable().__repr__()\n",
        AnalysisDialect::SoacStrictV1,
        false,
    );
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let facts =
        export_soac_module_facts(&db, file, "main", ResolvedStrictPolicy::default()).unwrap();
    assert!(
        facts
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
    );
    let record = class(&facts, "NonCallable");
    for name in ["__repr__", "__eq__"] {
        assert!(
            !record
                .transform
                .as_ref()
                .unwrap()
                .generated_methods
                .contains(name)
        );
        assert!(!record.methods.iter().any(|method| method.name == name));
    }
}

#[test]
fn soac_dataclass_kw_only_markers_are_not_storage_fields() {
    let source = r#"from __future__ import strict
from dataclasses import dataclass, KW_ONLY as Marker
from typing import ClassVar
@dataclass(init=False)
class Record:
    first: int = 1
    shared: ClassVar[int] = 2
    delimiter: Marker
    after: str = "value"
@dataclass
class WithInit:
    first: int = 1
    arbitrary_marker_name: Marker
    after: int = 2
@dataclass
class Base:
    delimiter: int = 3
@dataclass(init=False)
class Child(Base):
    delimiter: Marker
    after: int = 4
"#;
    for source in [
        source.to_owned(),
        source.replace("import strict", "import strict, annotations"),
    ] {
        let facts = export(&source);
        let record = class(&facts, "Record");
        assert!(
            !record
                .transform
                .as_ref()
                .unwrap()
                .dataclass_options
                .as_ref()
                .unwrap()
                .init
        );
        assert!(
            record
                .instance_fields
                .iter()
                .all(|field| field.name != "delimiter")
        );
        assert_eq!(
            record
                .instance_fields
                .iter()
                .filter(|field| field.field_kind != FieldKind::ClassVariable)
                .map(|field| field.name.as_str())
                .collect::<Vec<_>>(),
            ["first", "after"]
        );
        assert_eq!(
            record
                .instance_fields
                .iter()
                .find(|field| field.name == "shared")
                .unwrap()
                .field_kind,
            FieldKind::ClassVariable
        );
        let with_init = class(&facts, "WithInit");
        assert!(
            with_init
                .instance_fields
                .iter()
                .all(|field| field.name != "arbitrary_marker_name")
        );
        let init = with_init
            .methods
            .iter()
            .find(|method| method.name == "__init__")
            .unwrap();
        assert_eq!(
            init.signature
                .parameters
                .iter()
                .find(|parameter| parameter.name == "after")
                .unwrap()
                .kind,
            ParameterKind::KeywordOnly
        );
        let child = class(&facts, "Child");
        let inherited = child
            .instance_fields
            .iter()
            .find(|field| field.name == "delimiter")
            .unwrap();
        assert_eq!(
            inherited.declaring_class.definition.lexical_qualname,
            "Base"
        );
        assert_eq!(
            inherited.value_type,
            StaticType::NominalBuiltin {
                builtin: BuiltinType::Int,
                allow_subclasses: true
            }
        );
    }
}

#[test]
fn soac_dataclass_kw_only_exclusion_uses_semantic_marker_and_generator_role() {
    let source = r#"from __future__ import strict
from dataclasses import dataclass, KW_ONLY as Marker
class Plain:
    delimiter: Marker
class KW_ONLY:
    pass
@dataclass
class Namesake:
    real: KW_ONLY
@dataclass
class FieldName:
    KW_ONLY: int = 5
"#;
    let facts = export(source);
    assert!(
        class(&facts, "Plain")
            .instance_fields
            .iter()
            .any(|field| field.name == "delimiter")
    );
    let field = &class(&facts, "Namesake").instance_fields[0];
    assert_eq!(field.name, "real");
    let StaticType::NominalClass(reference) = &field.value_type else {
        panic!("a user class named KW_ONLY is a real nominal field");
    };
    assert_eq!(reference.definition.lexical_qualname, "KW_ONLY");
    let fields = &class(&facts, "FieldName").instance_fields;
    assert_eq!(fields.len(), 1);
    assert_eq!(fields[0].name, "KW_ONLY");
    assert_eq!(
        fields[0].value_type,
        StaticType::NominalBuiltin {
            builtin: BuiltinType::Int,
            allow_subclasses: true
        }
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
fn soac_export_builtin_bases_use_semantic_identity_in_direct_bases_and_mro() {
    let source = r#"from __future__ import strict
import builtins
from builtins import object as ImportedObject
Root = builtins.object
class Implicit:
    pass
class Explicit(object):
    pass
class Qualified(builtins.object):
    pass
class Imported(ImportedObject):
    pass
class Aliased(Root):
    pass
class Derived(Explicit):
    pass
def factory():
    class object:
        pass
    LocalRoot = object
    class Shadowed(LocalRoot):
        pass
    return object, Shadowed
"#;
    let facts = export(source);
    assert!(facts.diagnostics.iter().all(|diagnostic| {
        diagnostic.severity != DiagnosticSeverity::Error || diagnostic.suppressed
    }));
    let object = BaseReference::Builtin(BuiltinType::Object);
    for name in ["Implicit", "Explicit", "Qualified", "Imported", "Aliased"] {
        let class = class(&facts, name);
        assert_eq!(
            class.participation,
            ParticipationProposal::Candidate,
            "{name}"
        );
        assert!(class.inheritance.complete, "{name}");
        assert_eq!(class.inheritance.linearized_bases, vec![object.clone()]);
        assert_eq!(
            class.bases,
            if name == "Implicit" {
                vec![]
            } else {
                vec![object.clone()]
            },
            "{name}"
        );
    }
    let explicit = ClassReference {
        definition: class(&facts, "Explicit").identity.clone(),
        source_digest: facts.source_digest,
    };
    let derived = class(&facts, "Derived");
    assert_eq!(derived.bases, vec![BaseReference::Class(explicit.clone())]);
    assert_eq!(
        derived.inheritance.linearized_bases,
        vec![BaseReference::Class(explicit), object.clone()]
    );
    let shadow = ClassReference {
        definition: class(&facts, "factory.<locals>.object").identity.clone(),
        source_digest: facts.source_digest,
    };
    let shadowed = class(&facts, "factory.<locals>.Shadowed");
    assert_eq!(shadowed.participation, ParticipationProposal::Candidate);
    assert_eq!(shadowed.bases, vec![BaseReference::Class(shadow.clone())]);
    assert_eq!(
        shadowed.inheritance.linearized_bases,
        vec![BaseReference::Class(shadow), object]
    );
}

#[test]
fn soac_export_builtin_base_identity_does_not_grant_participation() {
    let facts = export(
        r#"from __future__ import strict
class IntChild(int):
    pass
class ListChild(list[int]):
    pass
class DictChild(dict[str, int]):
    pass
class Meta(type):
    pass
class Custom(metaclass=Meta):
    pass
class Child(Custom):
    pass
"#,
    );
    for (name, builtin) in [
        ("IntChild", BuiltinType::Int),
        ("ListChild", BuiltinType::List),
        ("DictChild", BuiltinType::Dict),
        ("Meta", BuiltinType::Type),
    ] {
        let class = class(&facts, name);
        assert_eq!(class.bases, vec![BaseReference::Builtin(builtin)]);
        // The logical typeshed MRO may include modeled ABCs which are not
        // physical CPython bases. Preserve those source references in place.
        assert_eq!(
            class.inheritance.linearized_bases.first(),
            Some(&BaseReference::Builtin(builtin))
        );
        assert_eq!(
            class.inheritance.linearized_bases.last(),
            Some(&BaseReference::Builtin(BuiltinType::Object))
        );
        assert!(
            matches!(&class.participation, ParticipationProposal::Dynamic(reasons)
            if reasons.contains(&DynamicClassReason::MutableBase)),
            "{name}"
        );
    }
    assert!(matches!(
        class(&facts, "Child").participation,
        ParticipationProposal::Dynamic(_)
    ));
}

#[test]
fn soac_export_builtin_base_alias_changes_invalidate_real_source_references() {
    let source = "from __future__ import strict\nfrom builtins import object as Root\nclass Base(Root): pass\n";
    let (mut db, system) = inheritance_database(source, false);
    let initial = export_from(&db);
    assert_eq!(
        class(&initial, "Child").participation,
        ParticipationProposal::Candidate
    );
    assert_eq!(
        class(&initial, "Child").inheritance.linearized_bases.last(),
        Some(&BaseReference::Builtin(BuiltinType::Object))
    );
    let changed = "from __future__ import strict\nclass object:\n    def __getattr__(self, name: str) -> int: return 1\nRoot = object\nclass Base(Root): pass\n";
    system
        .memory_file_system()
        .write_file_all("/project/base.py", changed)
        .unwrap();
    db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
        "/project/base.py".into(),
    )]);
    let updated = export_from(&db);
    let child = class(&updated, "Child");
    assert!(
        matches!(&child.participation, ParticipationProposal::Dynamic(reasons)
        if reasons.contains(&DynamicClassReason::MutableBase))
    );
    let shadow = child
        .inheritance
        .linearized_bases
        .iter()
        .filter_map(BaseReference::as_class)
        .find(|base| {
            base.definition.module.module_name == "base"
                && base.definition.lexical_qualname == "object"
        })
        .unwrap();
    assert_eq!(shadow.source_digest, Fingerprint::digest(changed));
    assert_eq!(
        child.inheritance.linearized_bases.last(),
        Some(&BaseReference::Builtin(BuiltinType::Object))
    );
    system
        .memory_file_system()
        .write_file_all("/project/base.py", source)
        .unwrap();
    db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
        "/project/base.py".into(),
    )]);
    assert_eq!(export_from(&db), initial);
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
    assert_eq!(
        child.bases[0]
            .as_class()
            .unwrap()
            .definition
            .module
            .module_name,
        "bridge"
    );
    let ancestor = child
        .inheritance
        .linearized_bases
        .iter()
        .filter_map(BaseReference::as_class)
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

#[test]
fn soac_source_surrogate_literals_fail_before_export() {
    for body in [
        r#"def value(): return '\ud800'"#,
        r#"def value(arg): return f'\ud800{arg}'"#,
        r#"def value(arg): return f'{arg:\ud800}'"#,
        r#"def value(arg): return t'\ud800{arg}'"#,
        r#"def value(arg): return t'{arg:\ud800}'"#,
        r#"from typing import Literal
def accept(value: Literal['\ud800']) -> Literal['\ud800']: return value"#,
    ] {
        let source = format!("from __future__ import strict\n{body}\n");
        let db = database(&source, AnalysisDialect::SoacStrictV1, false);
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        let error = export_soac_module(&db, file, "main", ResolvedStrictPolicy::default())
            .expect_err("unsupported source must not produce a proposal");
        assert!(matches!(&error, ContractError::InvalidSourceIdentity(_)));
        assert!(error.to_string().contains("unsupported Unicode surrogate escape U+D800"));
        let start = source.find(r"\ud800").unwrap();
        assert!(error.to_string().contains(&format!("bytes {start}..{}", start + 6)));
    }
}

#[test]
fn soac_source_genuine_replacement_and_raw_literals_remain_exact() {
    let facts = export(r#"from __future__ import strict
from typing import Literal
def accept(value: Literal['�'], raw: Literal[r'\ud800']) -> Literal['\ufffd']:
    return value
"#);
    let signature = &function(&facts, "accept").signature;
    assert_eq!(signature.parameters[0].value_type, StaticType::Literal(LiteralValue::Str("�".into())));
    assert_eq!(signature.parameters[1].value_type, StaticType::Literal(LiteralValue::Str(r"\ud800".into())));
    assert_eq!(signature.return_type, StaticType::Literal(LiteralValue::Str("�".into())));
}

fn source_literal_dependency_database(dependency: &str, main: &str) -> ProjectDatabase {
    let system = TestSystem::default();
    system.memory_file_system().write_files_all([
        ("/project/ty.toml", "[environment]\npython-version = '3.15'\n"),
        ("/project/dependency.py", dependency),
        ("/project/main.py", main),
    ]).unwrap();
    let metadata = ProjectMetadata::discover(
        ruff_db::system::SystemPath::new("/project"), &system,
    ).unwrap();
    ProjectDatabase::fallible_with_analysis_dialect(
        metadata, system, AnalysisDialect::SoacStrictV1,
    ).unwrap()
}

#[test]
fn soac_source_imported_surrogate_aliases_never_become_replacement_literal_facts() {
    let main = "from __future__ import strict\nfrom dependency import Alias\ndef accept(value: Alias) -> Alias: return value\n";
    for (dependency, expected) in [
        (r#"from typing import Literal
Alias = Literal['\ud800']
"#, StaticType::Unknown),
        (r#"from typing import Literal
type Alias = Literal['\U0000DFFF']
"#, StaticType::Unknown),
        (r#"from typing import Literal
Alias = Literal['�']
"#, StaticType::Literal(LiteralValue::Str("�".into()))),
        (r#"from typing import Literal
Alias = Literal[r'\ud800']
"#, StaticType::Literal(LiteralValue::Str(r"\ud800".into()))),
    ] {
        let db = source_literal_dependency_database(dependency, main);
        let facts = export_from(&db);
        let signature = &function(&facts, "accept").signature;
        assert_eq!(signature.parameters[0].value_type, expected, "{dependency}");
        assert_eq!(signature.return_type, expected, "{dependency}");
        if expected == StaticType::Unknown {
            assert!(signature.uncertainty.contains(&UncertaintyReason::Unknown));
        }
    }
}

#[test]
fn soac_source_dependency_f_and_t_strings_still_infer_interpolation_operands() {
    for prefix in ["f", "t"] {
        let dependency = format!("VALUE = {prefix}'\\ud800{{missing_operand}}'\n");
        let db = source_literal_dependency_database(
            &dependency,
            "from __future__ import strict\nfrom dependency import VALUE\nobserved = VALUE\n",
        );
        let file = system_path_to_file(&db, "/project/dependency.py").unwrap();
        let diagnostics = ty_python_semantic::Db::check_file(&db, file);
        let diagnostic = diagnostics.iter().find(|diagnostic| {
            diagnostic.id().is_lint_named("unresolved-reference")
        }).expect("interpolation expression is still analyzed");
        let range = diagnostic.primary_span().unwrap().range().unwrap();
        assert_eq!(&dependency[range], "missing_operand");
        let facts = export_from(&db);
        let observed = facts.global_bindings.iter().find(|binding| binding.name == "observed").unwrap();
        assert!(!matches!(observed.value_type, StaticType::Literal(_)));
    }
}


fn pydantic_export_database(source: &str) -> ProjectDatabase {
    let system = TestSystem::default();
    let project = SystemPathBuf::from("/project");
    system.memory_file_system().write_files_all([
        (
            project.join("ty.toml"),
            "[environment]\npython-version = '3.15'\nextra-paths = ['/dependencies']\n",
        ),
        (project.join("main.py"), source),
        (
            SystemPathBuf::from("/dependencies/pydantic/__init__.pyi"),
            "from .main import BaseModel as BaseModel\n",
        ),
        (
            SystemPathBuf::from("/dependencies/pydantic/main.pyi"),
            "from typing import dataclass_transform\n@dataclass_transform(kw_only_default=True)\nclass BaseModel: ...\n",
        ),
    ]).unwrap();
    let metadata = ProjectMetadata::discover(&project, &system).unwrap();
    ProjectDatabase::fallible_with_analysis_dialect(
        metadata, system, AnalysisDialect::SoacStrictV1,
    ).unwrap()
}

#[test]
fn soac_export_pydantic_fields_do_not_invent_source_owned_builtin_object_members() {
    let db = pydantic_export_database(
        "from __future__ import strict\nfrom pydantic import BaseModel\n\nclass Item(BaseModel):\n    id: int\n    name: str\n",
    );
    let facts = export_from(&db);
    let item = class(&facts, "Item");
    assert!(matches!(&item.participation, ParticipationProposal::Dynamic(reasons)
        if reasons.contains(&DynamicClassReason::FrameworkManaged)));
    assert!(item.inheritance.linearized_bases.contains(
        &BaseReference::Builtin(BuiltinType::Object),
    ));
    assert_eq!(
        item.instance_fields.iter().map(|field| field.name.as_str()).collect::<Vec<_>>(),
        ["id", "name"],
    );
    for field in &item.instance_fields {
        assert_eq!(field.declaring_class.definition, item.identity);
    }
    assert!(facts.diagnostics.iter().all(|diagnostic|
        diagnostic.suppressed || diagnostic.severity != DiagnosticSeverity::Error
    ));
}

#[test]
fn soac_export_pydantic_fields_keep_user_object_names_and_real_overrides() {
    let db = pydantic_export_database(
        "from __future__ import strict\nfrom pydantic import BaseModel\n\nclass object:\n    ordinary: int\n    __doc__: str | None\n\nclass Item(object, BaseModel):\n    id: int\n",
    );
    let facts = export_from(&db);
    let item = class(&facts, "Item");
    let user = class(&facts, "object");
    assert!(item.inheritance.linearized_bases.iter().any(
        |base| base.as_class().is_some_and(|base| base.definition == user.identity),
    ));
    for name in ["ordinary", "__doc__"] {
        assert_eq!(field(&facts, "Item", name).declaring_class.definition, user.identity);
    }
    assert_eq!(field(&facts, "Item", "id").declaring_class.definition, item.identity);
    assert!(facts.diagnostics.iter().all(|diagnostic|
        diagnostic.suppressed || diagnostic.severity != DiagnosticSeverity::Error
    ));
}


#[test]
fn soac_export_repeated_source_digests_refresh_after_same_size_dependency_changes() {
    let source = "from __future__ import strict\nclass Base: pass\ndef decorate[T](value: T) -> T: return value\n# first\n";
    let (mut db, system) = inheritance_database(source, false);
    let main = "from __future__ import strict\nfrom base import Base, decorate\nclass Child(Base):\n    left: Base\n    right: Base\n@decorate\nclass Decorated: pass\ndef echo(left: Base, right: Base) -> Base: return left\n";
    system.memory_file_system().write_file_all("/project/main.py", main).unwrap();
    db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
        "/project/main.py".into(),
    )]);

    fn assert_digests(facts: &ModuleTypeFacts, source: &str) {
        let expected = Fingerprint::digest(source);
        let base = class(facts, "Child").bases[0].as_class().unwrap();
        assert_eq!(base.source_digest, expected);
        for name in ["left", "right"] {
            let StaticType::NominalClass(reference) = &field(facts, "Child", name).value_type else {
                panic!("field must keep the actual nominal source reference");
            };
            assert_eq!(reference, base);
        }
        let signature = &function(facts, "echo").signature;
        assert_eq!(signature.parameters.len(), 2);
        for value_type in signature.parameters.iter().map(|parameter| &parameter.value_type)
            .chain([&signature.return_type])
        {
            let StaticType::NominalClass(reference) = value_type else {
                panic!("signature must keep the actual nominal source reference");
            };
            assert_eq!(reference, base);
        }
        let decorators = &class(facts, "Decorated").decorators;
        assert_eq!(decorators.len(), 1);
        assert_eq!(decorators[0].definition.as_ref().unwrap().module, base.definition.module);
        assert_eq!(decorators[0].source_digest, Some(expected));
        let dependencies: Vec<_> = facts.consumed_dependencies.iter()
            .filter(|dependency| dependency.module.module_name == "base").collect();
        assert_eq!(dependencies.len(), 1);
        assert_eq!(dependencies[0].module, base.definition.module);
        assert_eq!(dependencies[0].source_digest, expected);
        assert_eq!(dependencies[0].source_size as usize, source.len());
    }

    let initial = export_from(&db);
    assert_digests(&initial, source);
    assert_eq!(export_from(&db), initial, "repeated exports remain deterministic");
    let changed = source.replace("# first", "# other");
    assert_eq!(source.len(), changed.len());
    system.memory_file_system().write_file_all("/project/base.py", &changed).unwrap();
    db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
        "/project/base.py".into(),
    )]);
    let updated = export_from(&db);
    assert_digests(&updated, &changed);
    assert_ne!(updated, initial, "same file key and size do not preserve old digests");
    system.memory_file_system().write_file_all("/project/base.py", source).unwrap();
    db.apply_changes(&[crate::watch::ChangeEvent::file_content_changed(
        "/project/base.py".into(),
    )]);
    assert_eq!(export_from(&db), initial);
}


#[test]
fn soac_export_sys_modules_sentinel_writes_follow_stdlib_and_alias_types() {
    use ruff_db::diagnostic::Severity;

    let body = r#"import sys
from sys import modules as registry
from types import ModuleType

def install():
    sys.modules["direct"] = None
    registry["alias"] = None
    registry["ready"] = ModuleType("ready")
"#;
    for strict in [false, true] {
        let source = if strict {
            format!("from __future__ import strict\n{body}")
        } else {
            body.to_string()
        };
        let dialect = if strict {
            AnalysisDialect::SoacStrictV1
        } else {
            AnalysisDialect::Python
        };
        let db = database(&source, dialect, false);
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        let diagnostics = ty_python_semantic::Db::check_file(&db, file);
        assert!(
            diagnostics.iter().all(|diagnostic| !matches!(
                diagnostic.severity(),
                Severity::Error | Severity::Fatal
            )),
            "{diagnostics:?}"
        );
        if strict {
            let facts = export_from(&db);
            assert!(facts.diagnostics.iter().all(|diagnostic|
                diagnostic.severity != DiagnosticSeverity::Error
            ));
            let registry = facts.global_bindings.iter()
                .find(|binding| binding.name == "registry").unwrap();
            assert!(matches!(
                registry.value_type,
                StaticType::Unsupported {
                    kind: UnsupportedTypeKind::MutableGeneric,
                    ..
                }
            ), "mutable registry elements are not a protected module capability");
        }
    }
}

#[test]
fn soac_export_sys_modules_reads_stay_nullable_in_semantics_and_sites() {
    use ruff_python_ast::Stmt;
    use ty_python_semantic::types::Type;
    use ty_python_semantic::{HasType, SemanticModel};

    let source = r#"from __future__ import strict
import sys
from sys import modules as registry
from types import ModuleType

def fresh():
    return ModuleType("fresh")

def direct(name):
    return sys.modules[name]

def alias(name):
    return registry[name]

def read_name(name):
    return sys.modules[name].__name__

def invoke(name):
    return registry[name].callback()
"#;
    let db = database(source, AnalysisDialect::SoacStrictV1, false);
    let file = system_path_to_file(&db, "/project/main.py").unwrap();
    let program_file = ty_python_semantic::Db::program_file(&db, file);
    let model = SemanticModel::new(&db, program_file);
    let parsed = ruff_db::parsed::parsed_module(&db, program_file.python_file(&db))
        .load(&db);
    let mut returns = std::collections::BTreeMap::new();
    for statement in parsed.suite() {
        let Stmt::FunctionDef(definition) = statement else {
            continue;
        };
        let [Stmt::Return(return_statement)] = definition.body.as_slice() else {
            panic!("fixture functions have one explicit return");
        };
        let value = return_statement.value.as_deref().unwrap();
        returns.insert(
            definition.name.id.as_str(),
            value.inferred_type(&model).unwrap(),
        );
    }
    let module_type = returns["fresh"];
    assert!(matches!(module_type, Type::NominalInstance(_)));
    for name in ["direct", "alias"] {
        let Type::Union(union) = returns[name] else {
            panic!("registry lookup must preserve the nullable value union");
        };
        let elements = union.elements(&db);
        assert_eq!(elements.len(), 2);
        assert!(elements.contains(&module_type));
        assert_eq!(elements.iter().filter(|element| element.is_none(&db)).count(), 1);
    }

    let facts = export_proposal_from(&db);
    let reader = &function(&facts, "read_name").identity;
    let site = facts.attribute_sites.iter().find(|site|
        &site.identity.enclosing_function == reader && site.name == "__name__"
    ).unwrap();
    let StaticType::Union(alternatives) = &site.receiver_type else {
        panic!("export must retain the actual nullable receiver");
    };
    assert!(alternatives.contains(&StaticType::None));
    assert!(site.uncertainty.contains(&UncertaintyReason::OpenWorld));
    assert!(facts.diagnostics.iter().any(|diagnostic|
        diagnostic.code == DiagnosticCode::CheckerError
            && diagnostic.severity == DiagnosticSeverity::Error
            && diagnostic.source_range == site.identity.expression_range
            && !diagnostic.suppressed
    ), "the nullable module-attribute error must remain blocking");

    let invoker = &function(&facts, "invoke").identity;
    let calls: Vec<_> = facts.call_sites.iter().filter(|site|
        &site.identity.enclosing_function == invoker
    ).collect();
    assert_eq!(calls.len(), 1);
    assert_eq!(calls[0].binding, CallBindingFact::Dynamic);
    assert_eq!(calls[0].uncertainty, CallUncertainty::Dynamic);
    assert_eq!(calls[0].candidate_targets, vec![CallableTargetFact::Dynamic]);
    let actual_source = ruff_db::source::source_text(&db, file);
    assert!(matches!(
        validate_module_facts(&facts, Some(actual_source.as_bytes())),
        Err(ContractError::BlockingDiagnostic(_))
    ));
}

#[test]
fn soac_export_sys_modules_rejects_invalid_keys_and_values() {
    let body = r#"import sys
from sys import modules as registry

def invalid():
    sys.modules["number"] = 1
    registry["object"] = object()
    sys.modules[1] = None
"#;
    for strict in [false, true] {
        let source = if strict {
            format!("from __future__ import strict\n{body}")
        } else {
            body.to_string()
        };
        let dialect = if strict {
            AnalysisDialect::SoacStrictV1
        } else {
            AnalysisDialect::Python
        };
        let db = database(&source, dialect, false);
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        let diagnostics = ty_python_semantic::Db::check_file(&db, file);
        assert_eq!(
            diagnostics.iter().filter(|diagnostic|
                diagnostic.id().is_lint_named("invalid-assignment")
            ).count(),
            3,
            "{diagnostics:?}"
        );
        if strict {
            let facts = export_proposal_from(&db);
            assert_eq!(
                facts.diagnostics.iter().filter(|diagnostic|
                    diagnostic.code == DiagnosticCode::CheckerError
                        && diagnostic.severity == DiagnosticSeverity::Error
                        && !diagnostic.suppressed
                ).count(),
                3
            );
            let actual_source = ruff_db::source::source_text(&db, file);
            assert!(matches!(
                validate_module_facts(&facts, Some(actual_source.as_bytes())),
                Err(ContractError::BlockingDiagnostic(_))
            ));
        }
    }
}

#[test]
fn soac_export_sys_modules_user_registry_keeps_nonnullable_contract() {
    let body = r#"from types import ModuleType

class Namespace:
    modules: dict[str, ModuleType]

def invalid(sys: Namespace, registry: dict[str, ModuleType]):
    sys.modules["shadowed"] = None
    registry["ordinary"] = None
"#;
    for strict in [false, true] {
        let source = if strict {
            format!("from __future__ import strict\n{body}")
        } else {
            body.to_string()
        };
        let dialect = if strict {
            AnalysisDialect::SoacStrictV1
        } else {
            AnalysisDialect::Python
        };
        let db = database(&source, dialect, false);
        let file = system_path_to_file(&db, "/project/main.py").unwrap();
        let diagnostics = ty_python_semantic::Db::check_file(&db, file);
        assert_eq!(
            diagnostics.iter().filter(|diagnostic|
                diagnostic.id().is_lint_named("invalid-assignment")
            ).count(),
            2,
            "{diagnostics:?}"
        );
        if strict {
            let facts = export_proposal_from(&db);
            assert_eq!(
                facts.diagnostics.iter().filter(|diagnostic|
                    diagnostic.code == DiagnosticCode::CheckerError
                        && diagnostic.severity == DiagnosticSeverity::Error
                        && !diagnostic.suppressed
                ).count(),
                2
            );
            let actual_source = ruff_db::source::source_text(&db, file);
            assert!(matches!(
                validate_module_facts(&facts, Some(actual_source.as_bytes())),
                Err(ContractError::BlockingDiagnostic(_))
            ));
        }
    }
}
