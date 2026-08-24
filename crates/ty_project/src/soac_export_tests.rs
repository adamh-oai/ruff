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
            .filter(|leaf| leaf.function == function.identity)
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
            .filter(|leaf| leaf.function == function.identity)
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
                .all(|leaf| leaf.function != function.identity)
        );
    }
    let shadowed = function(&facts, "shadowed_factory.<locals>.inner");
    let local = class(&facts, "shadowed_factory.<locals>.Foreign");
    let leaves: Vec<_> = facts
        .nominal_bindings
        .iter()
        .filter(|leaf| leaf.function == shadowed.identity)
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
