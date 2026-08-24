//! Owned, source-bound SOAC proposals produced by the checker, not a second
//! annotation parser. All semantic decisions use the same inference, member,
//! decorator, dataclass and call-binding queries as ordinary ty checking.
//!
//! AST walks below locate source definitions and expression owners only. No
//! Salsa identity, rendered type, runtime layout or capability escapes this
//! module. The caller must authenticate the entire configured environment and
//! its dependencies before publishing these proposals.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};

use ruff_db::diagnostic::Severity;
use ruff_db::files::{File, FilePath};
use ruff_db::parsed::parsed_module;
use ruff_db::source::source_text;
use ruff_python_ast::{
    self as ast,
    visitor::{self, Visitor},
};
use ruff_text_size::{Ranged, TextRange};
use soac_contracts as facts;
use ty_module_resolver::file_to_module;
use ty_python_core::{
    AnalysisDialect, ProgramFile,
    definition::{Definition, DefinitionKind, ParameterDefinitionNodeKind},
    place_table,
    scope::{NodeWithScopeKind, ScopeId},
    semantic_index, use_def_map,
};

mod framework;
mod source;
pub(crate) use source::source_literals_supported;
mod strict;
pub(crate) use strict::register_lints;

use super::{
    CallArguments, ClassBase, ClassLiteral, DataclassFlags, DynamicType, KnownClass,
    LiteralValueTypeKind, ProgramEnvironment, Signature, Type, TypeQualifiers,
    class::{CodeGeneratorKind, FieldKind as TyFieldKind, StaticClassLiteral},
    function::{FunctionDecorators, KnownFunction},
    ide_support::{ImportAliasResolution, definitions_for_name},
    infer::{infer_definition_types, original_class_type},
    list_members::all_end_of_scope_members,
    signatures::{Parameter as TyParameter, ParameterKind as TyParameterKind},
};
use crate::place::{Place, TypeOrigin, place_from_bindings};
use crate::{Db, HasDefinition, HasType, SemanticModel};

/// An owned source path, never a Salsa file key. Virtual editor files are not
/// supported by the offline artifact path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SoacDependencyPath {
    System(String),
    Vendored(String),
}

/// The actual source behind an external semantic definition referenced by a
/// proposal. The driver supplies project policy and configuration fingerprints;
/// it must not reconstruct a different module resolution from import spelling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SoacSourceDependency {
    pub module: facts::ModuleContentId,
    pub source_digest: facts::Fingerprint,
    pub source_size: u32,
    pub path: SoacDependencyPath,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SoacModuleExport {
    pub facts: facts::ModuleTypeFacts,
    pub dependencies: Vec<SoacSourceDependency>,
}

/// Export just the checker predictions. Artifact producers should prefer
/// [`export_soac_module`] so they also obtain the actual dependency source paths.
pub fn export_soac_module_facts(
    db: &dyn Db,
    file: File,
    module_name: &str,
    policy: facts::ResolvedStrictPolicy,
) -> Result<facts::ModuleTypeFacts, facts::ContractError> {
    export_soac_module(db, file, module_name, policy).map(|export| export.facts)
}

/// Export checker predictions and their external source dependencies.
///
/// Requires an explicitly selected SOAC database. Ordinary Python files in
/// that database remain ordinary; importing a strict module never opts its
/// importer in. Diagnostics and ignored regions remain in the artifact.
/// This query neither signs facts nor constructs any runtime capability.
/// `consumed_dependencies` is left empty: the project exporter must bind each
/// external source reference to its resolved configuration, source and policy
/// fingerprints before calling `validate_module_facts` or encoding a shard.
pub fn export_soac_module(
    db: &dyn Db,
    file: File,
    module_name: &str,
    policy: facts::ResolvedStrictPolicy,
) -> Result<SoacModuleExport, facts::ContractError> {
    export_soac_module_impl(db, file, module_name, policy, true)
}

fn export_soac_module_impl(
    db: &dyn Db,
    file: File,
    module_name: &str,
    policy: facts::ResolvedStrictPolicy,
    resolve_external_bases: bool,
) -> Result<SoacModuleExport, facts::ContractError> {
    let program_file = db.program_file(file);
    if program_file.analysis_policy(db).dialect != AnalysisDialect::SoacStrictV1 {
        return Err(facts::ContractError::InvalidPolicy(
            "SOAC facts require an explicitly selected SOAC analysis database".into(),
        ));
    }
    let source = source_text(db, file);
    if source.read_error().is_some() {
        return Err(facts::ContractError::InvalidSourceIdentity(
            "source is unreadable".into(),
        ));
    }
    let parsed = parsed_module(db, program_file.python_file(db)).load(db);
    let index = semantic_index(db, program_file);
    if !parsed.errors().is_empty()
        || !parsed.unsupported_syntax_errors().is_empty()
        || !index.semantic_syntax_errors().is_empty()
    {
        return Err(facts::ContractError::InvalidSourceIdentity(
            "source is not valid in the selected checker dialect and Python version".into(),
        ));
    }
    let strict = parsed.suite().iter().any(|statement| {
        matches!(statement, ast::Stmt::ImportFrom(import)
            if import.level == 0 && import.module.as_deref() == Some("__future__")
                && import.names.iter().any(|alias| alias.name.as_str() == "strict"))
    });
    if strict {
        soac_source::validate_source_literals(source.as_str(), parsed.tokens()).map_err(|error| {
            facts::ContractError::InvalidSourceIdentity(error.to_string())
        })?;
    }
    let module = facts::ModuleTypeFacts::new(
        module_name,
        source.as_bytes(),
        if strict {
            facts::SourceDialect::SoacStrict
        } else {
            facts::SourceDialect::OrdinaryPython
        },
        policy,
    )?;
    let owner = module.module_body_identity();
    let mut exporter = Exporter {
        db,
        model: SemanticModel::new(db, program_file),
        env: ProgramEnvironment::from_file(program_file),
        module,
        owner,
        dependencies: RefCell::new(BTreeMap::new()),
        invalid_dependency: Cell::new(false),
        used_suppressions: Vec::new(),
        attribute_receivers: BTreeMap::new(),
        resolve_external_bases,
    };
    exporter.globals(program_file);
    exporter.visit_body(parsed.suite());
    // ty deliberately does not construct diagnostics that an ignore suppresses.
    // Retain the parser's covered *code* ranges, rather than guessing at an
    // omitted error from diagnostic text or scanning comments with a regexp.
    for range in
        crate::suppression::suppressions(db, program_file.python_file(db)).soac_covered_ranges()
    {
        let range = source_range(range);
        exporter.module.diagnostics.push(facts::StrictDiagnostic {
            code: facts::DiagnosticCode::StrictUncheckedDynamicType,
            severity: facts::DiagnosticSeverity::Warning,
            source_range: range,
            scope: facts::DiagnosticScope::Site(range),
            related_definitions: Vec::new(),
            suppressed: true,
            message: "Checker ignore covers this source region; dependent facts remain uncertain"
                .into(),
        });
    }
    // Suppressed source regions and dynamic base classes must be classified
    // before optional strict class diagnostics consult the proposal catalog.
    exporter.module = exporter.module.canonicalized()?;
    strict::check(&mut exporter, parsed.suite());
    // Complete the real checker diagnostic/suppression pipeline with the
    // explicit SOAC consumer's usage. This prevents a used strict ignore from
    // spuriously becoming an unused-ignore error, without suppressing unrelated
    // unused codes or changing ordinary Python checking.
    for diagnostic in super::check_types_with_suppression_usage(
        db,
        program_file,
        std::mem::take(&mut exporter.used_suppressions),
    ) {
        let framework_receiver = exporter.framework_attribute_fallback(&diagnostic);
        let absent_mutable_global =
            strict::reconcile_absent_global_diagnostic(&mut exporter, &diagnostic);
        let dynamic_warning = framework_receiver.is_some() || absent_mutable_global;
        let range = diagnostic
            .primary_span()
            .and_then(|span| span.range())
            .map(source_range)
            .unwrap_or(facts::SourceRange::new(0, source.len() as u32));
        exporter.module.diagnostics.push(facts::StrictDiagnostic {
            code: if dynamic_warning {
                facts::DiagnosticCode::StrictUncheckedDynamicType
            } else {
                facts::DiagnosticCode::CheckerError
            },
            severity: if dynamic_warning {
                facts::DiagnosticSeverity::Warning
            } else {
                match diagnostic.severity() {
                    Severity::Error | Severity::Fatal => facts::DiagnosticSeverity::Error,
                    Severity::Warning => facts::DiagnosticSeverity::Warning,
                    _ => facts::DiagnosticSeverity::Information,
                }
            },
            source_range: range,
            scope: facts::DiagnosticScope::Site(range),
            related_definitions: framework_receiver.iter().cloned().collect(),
            suppressed: false,
            message: if framework_receiver.is_some() {
                format!(
                    "{}: {}; SOAC retains dynamic framework attribute access",
                    diagnostic.id(),
                    diagnostic.headline_message()
                )
            } else if absent_mutable_global {
                format!(
                    "{}: {}; SOAC permits this syntactically declared mutable global; its value and boundness remain unknown",
                    diagnostic.id(),
                    diagnostic.headline_message()
                )
            } else {
                format!("{}: {}", diagnostic.id(), diagnostic.headline_message())
            },
        });
    }
    exporter.collect_import_dependencies(program_file);
    if exporter.invalid_dependency.get() {
        return Err(facts::ContractError::InvalidSourceIdentity(
            "a semantic dependency has a virtual path or conflicting source identities".into(),
        ));
    }
    Ok(SoacModuleExport {
        facts: exporter.module.canonicalized()?,
        dependencies: exporter.dependencies.into_inner().into_values().collect(),
    })
}

struct Exporter<'db> {
    db: &'db dyn Db,
    model: SemanticModel<'db>,
    env: ProgramEnvironment<'db>,
    module: facts::ModuleTypeFacts,
    owner: facts::SourceIdentity,
    dependencies: RefCell<BTreeMap<String, SoacSourceDependency>>,
    invalid_dependency: Cell<bool>,
    used_suppressions: Vec<crate::suppression::FileSuppressionId>,
    /// Private semantic receivers indexed by their exact expression ranges.
    /// They do not escape into the owned proposal DTO.
    attribute_receivers: BTreeMap<facts::SourceRange, Type<'db>>,
    /// The incremental base query first computes local proposals using this
    /// same classifier, then combines the actual semantic MRO recursively.
    /// Disabling this step internally avoids unrelated classes in an imported
    /// module introducing artificial recursion into the selected base query.
    resolve_external_bases: bool,
}

/// Class location is not evidence that its bindings remain mutable. Reuse the
/// complete semantic classifier and suppression normalization for the defining
/// file, then require candidate proposals throughout the real resolved MRO.
/// The query publishes only a logical proposal, never runtime base authority.
#[salsa::tracked(
    returns(copy),
    cycle_initial=|_, _, _| false,
    heap_size=ruff_memory_usage::heap_size,
)]
fn external_strict_base_is_candidate<'db>(db: &'db dyn Db, class: StaticClassLiteral<'db>) -> bool {
    let file = class.program_file(db);
    let Some(module) = file_to_module(db, file.resolver_file(db)) else {
        return false;
    };
    // The four-argument public export API has only the importing file's
    // effective policy. Do not apply that policy to another file's transform.
    // External dataclasses remain dynamic until an explicit per-file adapter
    // policy context is available. Plain strict classes need no such adapter.
    let mut policy = facts::ResolvedStrictPolicy::default();
    policy.adapters.dataclasses = facts::StdlibDataclassPolicy::Dynamic;
    let Ok(export) =
        export_soac_module_impl(db, file.file(db), module.name(db).as_str(), policy, false)
    else {
        return false;
    };
    if export.facts.source_dialect != facts::SourceDialect::SoacStrict
        || export.facts.diagnostics.iter().any(|diagnostic| {
            !diagnostic.suppressed && diagnostic.severity == facts::DiagnosticSeverity::Error
        })
    {
        return false;
    }
    let parsed = parsed_module(db, file.python_file(db)).load(db);
    let definition_range = source_range(class.definition(db).kind(db).full_range(&parsed));
    if !export.facts.classes.iter().any(|proposal| {
        proposal.identity.source_range == definition_range
            && proposal.participation == facts::ParticipationProposal::Candidate
    }) || class.try_mro(db, None).is_err()
    {
        return false;
    }
    class.iter_mro(db, None).skip(1).all(|base| match base {
        ClassBase::Class(base) if base.known(db) == Some(KnownClass::Object) => true,
        ClassBase::Class(base) => base
            .class_literal(db)
            .as_static()
            .is_some_and(|base| external_strict_base_is_candidate(db, base)),
        _ => false,
    })
}

fn source_range(range: TextRange) -> facts::SourceRange {
    facts::SourceRange::new(range.start().to_u32(), range.end().to_u32())
}

fn unsupported(kind: facts::UnsupportedTypeKind) -> facts::StaticType {
    facts::StaticType::Unsupported {
        kind,
        reason: facts::UnsupportedReasonCode::NoRuntimeEnforcement,
    }
}

/// Only the checker's resolved builtin identity selects this projection. A
/// source class or alias spelled `object` does not establish a builtin base.
fn builtin_type(known: KnownClass) -> Option<facts::BuiltinType> {
    use facts::BuiltinType as B;
    Some(match known {
        KnownClass::Object => B::Object,
        KnownClass::Bool => B::Bool,
        KnownClass::Int => B::Int,
        KnownClass::Float => B::Float,
        KnownClass::Complex => B::Complex,
        KnownClass::Str => B::Str,
        KnownClass::Bytes => B::Bytes,
        KnownClass::Bytearray => B::ByteArray,
        KnownClass::List => B::List,
        KnownClass::Dict => B::Dict,
        KnownClass::Set => B::Set,
        KnownClass::FrozenSet => B::FrozenSet,
        KnownClass::Tuple => B::Tuple,
        KnownClass::Type => B::Type,
        _ => return None,
    })
}

fn uncertainty(ty: &facts::StaticType) -> BTreeSet<facts::UncertaintyReason> {
    use facts::{StaticType as S, UncertaintyReason as U};
    match ty {
        S::Any => BTreeSet::from([U::Any]),
        S::Unknown => BTreeSet::from([U::Unknown]),
        S::Todo => BTreeSet::from([U::CheckerTodo]),
        S::Union(items) => items.iter().flat_map(uncertainty).collect(),
        S::Optional(inner) => uncertainty(inner),
        S::Callable(signature) => signature.uncertainty.clone(),
        ty if ty.contains_uncertainty() => BTreeSet::from([U::UnsupportedType]),
        _ => BTreeSet::new(),
    }
}

fn unknown_signature() -> facts::CallableSignature {
    facts::CallableSignature {
        parameters: Vec::new(),
        return_type: facts::StaticType::Unknown,
        return_annotation_origin: facts::AnnotationOrigin::Unresolved,
        uncertainty: BTreeSet::from([facts::UncertaintyReason::Unknown]),
    }
}

impl<'db> Exporter<'db> {
    /// Conservative resolved import closure. A dependency can determine a
    /// builtin-valued fact without leaving a nominal source reference in the
    /// exported type (for example `from configuration import NUMBER`). Resolve
    /// those imports inside the actual checker program as well.
    fn collect_import_dependencies(&self, file: ProgramFile<'db>) {
        struct Imports<'a, 'db> {
            exporter: &'a Exporter<'db>,
            model: SemanticModel<'db>,
            files: Vec<ProgramFile<'db>>,
        }
        impl<'db> Imports<'_, 'db> {
            fn module(&mut self, module: Option<ty_module_resolver::Module<'db>>) {
                if let Some(file) = module.and_then(|module| module.file(self.exporter.db)) {
                    self.files
                        .push(self.model.program().program_file(self.exporter.db, file));
                }
            }
            fn alias(&mut self, alias: &ast::Alias) {
                if let Some(Type::ModuleLiteral(module)) = alias.inferred_type(&self.model) {
                    self.module(Some(module.module(self.exporter.db)));
                }
            }
        }
        impl<'ast> Visitor<'ast> for Imports<'_, '_> {
            fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
                match statement {
                    ast::Stmt::Import(import) => {
                        for alias in &import.names {
                            self.module(self.model.resolve_module(Some(alias.name.as_str()), 0));
                            self.alias(alias);
                        }
                    }
                    ast::Stmt::ImportFrom(import) => {
                        self.module(
                            self.model
                                .resolve_module(import.module.as_deref(), import.level),
                        );
                        for alias in &import.names {
                            self.alias(alias);
                        }
                    }
                    _ => {}
                }
                visitor::walk_stmt(self, statement);
            }
        }
        let mut pending = vec![file];
        let mut visited = rustc_hash::FxHashSet::default();
        while let Some(file) = pending.pop() {
            if !visited.insert(file) {
                continue;
            }
            let _ = self.module_id(file);
            let parsed = parsed_module(self.db, file.python_file(self.db)).load(self.db);
            if !parsed.errors().is_empty() {
                continue;
            }
            let mut imports = Imports {
                exporter: self,
                model: SemanticModel::new(self.db, file),
                files: Vec::new(),
            };
            imports.module(imports.model.resolve_module(Some("builtins"), 0));
            imports.visit_body(parsed.suite());
            pending.extend(imports.files);
        }
    }

    fn module_id(&self, file: ProgramFile<'db>) -> Option<facts::ModuleContentId> {
        if file.file(self.db) == self.model.file() {
            return Some(self.module.module.clone());
        }
        let module = file_to_module(self.db, file.resolver_file(self.db))?;
        let source = source_text(self.db, file.file(self.db));
        if source.read_error().is_some() {
            return None;
        }
        let identity = facts::ModuleContentId::new(
            module.name(self.db).as_str(),
            facts::legacy_source_hash(source.as_bytes()),
        );
        let path = match file.file(self.db).path(self.db) {
            FilePath::System(path) => SoacDependencyPath::System(path.as_str().to_owned()),
            FilePath::Vendored(path) => SoacDependencyPath::Vendored(path.as_str().to_owned()),
            FilePath::SystemVirtual(_) => {
                self.invalid_dependency.set(true);
                return None;
            }
        };
        let source_size = u32::try_from(source.len()).ok()?;
        let dependency = SoacSourceDependency {
            module: identity.clone(),
            source_digest: facts::Fingerprint::digest(source.as_bytes()),
            source_size,
            path,
        };
        let mut dependencies = self.dependencies.borrow_mut();
        if let Some(previous) = dependencies.get(&identity.module_name) {
            if previous != &dependency {
                self.invalid_dependency.set(true);
            }
        } else {
            dependencies.insert(identity.module_name.clone(), dependency);
        }
        Some(identity)
    }

    fn definition(&self, definition: Definition<'db>) -> Option<facts::SourceIdentity> {
        let db = self.db;
        let program_file = definition.program_file(db);
        let parsed = parsed_module(db, program_file.python_file(db)).load(db);
        let (kind, name) = match definition.kind(db) {
            DefinitionKind::Class(node) => (
                facts::DefinitionKind::Class,
                node.node(&parsed).name.to_string(),
            ),
            DefinitionKind::Function(node) => (
                facts::DefinitionKind::Function,
                node.node(&parsed).name.to_string(),
            ),
            DefinitionKind::Parameter(_) => {
                (facts::DefinitionKind::Parameter, "<parameter>".into())
            }
            DefinitionKind::TypeVar(node) => (
                facts::DefinitionKind::Parameter,
                node.node(&parsed).name.to_string(),
            ),
            DefinitionKind::ParamSpec(node) => (
                facts::DefinitionKind::Parameter,
                node.node(&parsed).name.to_string(),
            ),
            DefinitionKind::TypeVarTuple(node) => (
                facts::DefinitionKind::Parameter,
                node.node(&parsed).name.to_string(),
            ),
            DefinitionKind::TypeAlias(_) => {
                (facts::DefinitionKind::TypeAlias, definition.name(db)?)
            }
            _ => (
                facts::DefinitionKind::Assignment,
                definition.name(db).unwrap_or_else(|| "<binding>".into()),
            ),
        };
        Some(facts::SourceIdentity {
            module: self.module_id(program_file)?,
            lexical_qualname: self.lexical_qualname(definition.scope(db), name),
            source_range: source_range(definition.kind(db).full_range(&parsed)),
            definition_kind: kind,
        })
    }

    /// Source identities use actual semantic lexical ancestry. Comprehension
    /// scopes are transparent here; native code-object names are a separate
    /// compiler projection, not inferred from an expression visitor's owner.
    fn lexical_qualname(&self, scope: ScopeId<'db>, name: String) -> String {
        let db = self.db;
        let program_file = scope.program_file(db);
        let parsed = parsed_module(db, program_file.python_file(db)).load(db);
        let mut ancestors = Vec::new();
        let mut scope = Some(scope);
        while let Some(current) = scope {
            match current.node(db) {
                NodeWithScopeKind::Class(node) => {
                    ancestors.push(node.node(&parsed).name.to_string())
                }
                NodeWithScopeKind::Function(node) => {
                    ancestors.push(format!("{}.<locals>", node.node(&parsed).name))
                }
                NodeWithScopeKind::Lambda(_) => ancestors.push("<lambda>".into()),
                _ => {}
            }
            scope = current
                .scope(db)
                .parent()
                .map(|parent| parent.to_scope_id(db, program_file));
        }
        ancestors.reverse();
        ancestors.push(name);
        ancestors.join(".")
    }

    fn class_reference(&self, class: ClassLiteral<'db>) -> Option<facts::ClassReference> {
        let class = class.as_static()?;
        Some(facts::ClassReference {
            definition: self.definition(class.definition(self.db))?,
            source_digest: facts::Fingerprint::digest(
                source_text(self.db, class.file(self.db)).as_bytes(),
            ),
        })
    }

    fn base_reference(&self, class: ClassLiteral<'db>) -> Option<facts::BaseReference> {
        class
            .known(self.db)
            .and_then(builtin_type)
            .map(facts::BaseReference::Builtin)
            .or_else(|| self.class_reference(class).map(facts::BaseReference::Class))
    }

    fn value_type(&self, ty: Type<'db>) -> facts::StaticType {
        self.value_type_at_depth(ty, 0)
    }

    fn value_type_at_depth(&self, ty: Type<'db>, depth: usize) -> facts::StaticType {
        use facts::{BuiltinType as B, StaticType as S, UnsupportedTypeKind as U};
        if depth >= 32 {
            return unsupported(U::RecursiveType);
        }
        match ty {
            Type::Dynamic(DynamicType::Any) => S::Any,
            Type::Dynamic(DynamicType::Todo(_)) => S::Todo,
            Type::Dynamic(_) => S::Unknown,
            Type::Divergent(_) | Type::Never => S::Divergent,
            Type::Union(union) => {
                let mut elements: Vec<_> = union
                    .elements(self.db)
                    .iter()
                    .map(|ty| self.value_type_at_depth(*ty, depth + 1))
                    .collect();
                // ty expands numeric annotations into accepted nominal types.
                // Keep the shared schema's one numeric acceptance contract,
                // without erasing Any, Unknown or other union alternatives.
                let numeric = elements
                    .iter()
                    .filter_map(|element| {
                        if let S::NumericWidening { target, accepted } = element {
                            Some((*target, accepted.clone()))
                        } else {
                            None
                        }
                    })
                    .max_by_key(|(_, accepted)| accepted.len());
                if let Some((target, accepted)) = numeric {
                    elements.retain(|element| match element {
                        S::NominalBuiltin { builtin, .. } => !accepted.contains(builtin),
                        S::NumericWidening { target: other, .. } => *other == target,
                        _ => true,
                    });
                }
                if elements.len() == 1 {
                    elements.pop().unwrap()
                } else {
                    S::Union(elements)
                }
            }
            Type::TypeAlias(alias) => {
                self.value_type_at_depth(alias.value_type(self.db), depth + 1)
            }
            Type::TypeVar(bound) => {
                let variable = bound.typevar(self.db);
                let Some(identity) = variable
                    .definition(self.db)
                    .and_then(|definition| self.definition(definition))
                else {
                    return unsupported(U::Other);
                };
                let (upper_bound, constraints) =
                    match variable.bound_or_constraints(self.db, &self.env) {
                        Some(super::TypeVarBoundOrConstraints::UpperBound(bound)) => (
                            Some(Box::new(self.value_type_at_depth(bound, depth + 1))),
                            Vec::new(),
                        ),
                        Some(super::TypeVarBoundOrConstraints::Constraints(constraints)) => (
                            None,
                            constraints
                                .elements(self.db)
                                .iter()
                                .map(|ty| self.value_type_at_depth(*ty, depth + 1))
                                .collect(),
                        ),
                        None => (None, Vec::new()),
                    };
                S::TypeVariable(facts::TypeVariableFact {
                    identity,
                    upper_bound,
                    constraints,
                })
            }
            Type::NominalInstance(instance) => {
                let known = instance.known_class(self.db);
                if known == Some(KnownClass::NoneType) {
                    return S::None;
                }
                if instance.is_definition_generic(self.db) {
                    return unsupported(
                        if matches!(
                            known,
                            Some(KnownClass::List | KnownClass::Dict | KnownClass::Set)
                        ) {
                            U::MutableGeneric
                        } else {
                            U::GenericAlias
                        },
                    );
                }
                let builtin = known.and_then(builtin_type);
                match builtin {
                    Some(B::Float) => S::NumericWidening {
                        target: B::Float,
                        accepted: BTreeSet::from([B::Int, B::Float]),
                    },
                    Some(B::Complex) => S::NumericWidening {
                        target: B::Complex,
                        accepted: BTreeSet::from([B::Int, B::Float, B::Complex]),
                    },
                    Some(builtin) => S::NominalBuiltin {
                        builtin,
                        allow_subclasses: true,
                    },
                    None => self
                        .class_reference(instance.class_literal(self.db, &self.env))
                        .map(S::NominalClass)
                        .unwrap_or(S::Unknown),
                }
            }
            Type::ProtocolInstance(protocol) => {
                let origin = protocol.class_origin(self.db);
                S::StructuralProtocol(facts::ProtocolFact {
                    definition: origin
                        .and_then(|origin| self.class_reference(origin.class_literal(self.db))),
                    runtime_checkable: origin
                        .is_some_and(|origin| origin.is_runtime_checkable(self.db)),
                })
            }
            Type::LiteralValue(literal) => match literal.kind() {
                LiteralValueTypeKind::Bool(value) => S::Literal(facts::LiteralValue::Bool(value)),
                LiteralValueTypeKind::Int(value) => {
                    S::Literal(facts::LiteralValue::Int(value.as_i64().to_string()))
                }
                LiteralValueTypeKind::String(value) => {
                    S::Literal(facts::LiteralValue::Str(value.value(self.db).to_owned()))
                }
                LiteralValueTypeKind::Bytes(value) => {
                    S::Literal(facts::LiteralValue::Bytes(value.value(self.db).to_vec()))
                }
                _ => unsupported(U::Other),
            },
            Type::Callable(_) | Type::FunctionLiteral(_) | Type::BoundMethod(_) => {
                // Recursive callable aliases remain unsupported instead of
                // recursively serializing the checker's interned graph.
                if depth > 12 {
                    return unsupported(U::RecursiveType);
                }
                S::Callable(Box::new(self.callable_signature(ty, depth + 1)))
            }
            Type::ClassLiteral(_) | Type::SubclassOf(_) => S::NominalBuiltin {
                builtin: B::Type,
                allow_subclasses: true,
            },
            Type::GenericAlias(_) => unsupported(U::GenericAlias),
            Type::Intersection(_) => unsupported(U::Intersection),
            Type::TypeGuard(_) => unsupported(U::TypeGuard),
            Type::TypeIs(_) => unsupported(U::TypeIs),
            Type::TypedDict(_) => unsupported(U::TypedDict),
            Type::NewTypeInstance(_) => unsupported(U::NewType),
            _ => unsupported(U::Other),
        }
    }

    fn callable_signature(&self, ty: Type<'db>, depth: usize) -> facts::CallableSignature {
        let Some(callable) = ty
            .try_upcast_to_callable(self.db, &self.env)
            .and_then(|types| types.exactly_one())
        else {
            return unknown_signature();
        };
        let signatures = callable.signatures(self.db);
        // A single-signature schema cannot claim one arbitrarily chosen overload.
        match signatures.overloads.as_slice() {
            [signature] => self.signature(signature, depth),
            _ => unknown_signature(),
        }
    }

    fn signature(&self, signature: &Signature<'db>, depth: usize) -> facts::CallableSignature {
        let named_parameters: BTreeSet<_> = signature
            .parameters()
            .iter()
            .filter_map(|parameter| parameter.name().map(|name| name.as_str()))
            .collect();
        let parameters = signature
            .parameters()
            .iter()
            .enumerate()
            .map(|(index, parameter)| facts::ParameterTypeFact {
                name: parameter
                    .name()
                    .map(ToString::to_string)
                    .unwrap_or_else(|| {
                        // Unnamed semantic slots need a stable DTO label, not a
                        // guessed native parameter name. Never collide with an
                        // actual parameter (for example a dataclass field `arg0`).
                        let mut name = format!("arg{index}");
                        while named_parameters.contains(name.as_str()) {
                            name.push('_');
                        }
                        name
                    }),
                kind: match parameter.kind() {
                    TyParameterKind::PositionalOnly { .. } => facts::ParameterKind::PositionalOnly,
                    TyParameterKind::PositionalOrKeyword { .. } => {
                        facts::ParameterKind::PositionalOrKeyword
                    }
                    TyParameterKind::Variadic { .. } => facts::ParameterKind::VarArgs,
                    TyParameterKind::KeywordOnly { .. } => facts::ParameterKind::KeywordOnly,
                    TyParameterKind::KeywordVariadic { .. } => facts::ParameterKind::VarKeywords,
                },
                value_type: self.value_type_at_depth(parameter.annotated_type(), depth + 1),
                annotation_origin: self.parameter_annotation_origin(parameter),
                default: parameter
                    .default_type(self.db)
                    .map_or(facts::DefaultFact::Missing, |ty| self.default_value(ty)),
            })
            .collect::<Vec<_>>();
        let return_type = self.value_type_at_depth(signature.return_ty, depth + 1);
        let mut signature_uncertainty = uncertainty(&return_type);
        signature_uncertainty.extend(
            parameters
                .iter()
                .flat_map(|parameter| uncertainty(&parameter.value_type)),
        );
        let return_annotation_origin = signature
            .definition()
            .map(|definition| {
                let parsed = parsed_module(self.db, definition.python_file(self.db)).load(self.db);
                match definition.kind(self.db) {
                    DefinitionKind::Function(node) if node.node(&parsed).returns.is_some() => {
                        facts::AnnotationOrigin::Explicit
                    }
                    DefinitionKind::Function(_) => facts::AnnotationOrigin::Absent,
                    _ => facts::AnnotationOrigin::Inferred,
                }
            })
            .unwrap_or(facts::AnnotationOrigin::Inferred);
        facts::CallableSignature {
            parameters,
            return_type,
            return_annotation_origin,
            uncertainty: signature_uncertainty,
        }
    }

    fn default_value(&self, ty: Type<'db>) -> facts::DefaultFact {
        let ty = self.value_type(ty);
        let literal = match &ty {
            facts::StaticType::Literal(value) => Some(value.clone()),
            facts::StaticType::None => Some(facts::LiteralValue::None),
            _ => None,
        };
        facts::DefaultFact::Value {
            value_type: Box::new(ty),
            literal,
        }
    }

    fn parameter_annotation_origin(&self, parameter: &TyParameter<'db>) -> facts::AnnotationOrigin {
        // `inferred_annotation` controls signature display, not source provenance.
        // Synthesized self/other parameters also use with_annotated_type, but
        // their useful checker types must not manufacture mandatory checks.
        let Some(definition) = parameter.definition() else {
            return facts::AnnotationOrigin::Inferred;
        };
        match definition.kind(self.db) {
            DefinitionKind::Parameter(parameter) => {
                let parsed = parsed_module(self.db, definition.python_file(self.db)).load(self.db);
                let annotated = match parameter {
                    ParameterDefinitionNodeKind::Parameter(parameter) => {
                        parameter.node(&parsed).parameter.annotation.is_some()
                    }
                    ParameterDefinitionNodeKind::VariadicPositionalParameter(parameter)
                    | ParameterDefinitionNodeKind::VariadicKeywordParameter(parameter) => {
                        parameter.node(&parsed).annotation.is_some()
                    }
                };
                if annotated {
                    facts::AnnotationOrigin::Explicit
                } else {
                    facts::AnnotationOrigin::Inferred
                }
            }
            // Dataclass-generated field parameters carry the actual first
            // declaration, including inherited and InitVar fields. Preserve
            // that declaration's origin instead of guessing from a name.
            DefinitionKind::AnnotatedAssignment(_) => {
                self.field_annotation_origin(Some(definition))
            }
            _ => facts::AnnotationOrigin::Inferred,
        }
    }

    fn decorators(&self, decorators: &[ast::Decorator]) -> Vec<facts::DecoratorFact> {
        decorators
            .iter()
            .rev()
            .map(|decorator| {
                let result = decorator
                    .expression
                    .inferred_type(&self.model)
                    .unwrap_or_else(Type::unknown);
                let callee = match &decorator.expression {
                    ast::Expr::Call(call) => &*call.func,
                    expression => expression,
                };
                let callee_ty = callee
                    .inferred_type(&self.model)
                    .unwrap_or_else(Type::unknown);
                let mut definition = None;
                let kind = match callee_ty {
                    Type::FunctionLiteral(function) => {
                        definition = self.definition(function.definition(self.db));
                        match function.known(self.db) {
                            Some(KnownFunction::Dataclass) => facts::DecoratorKind::StdlibDataclass,
                            Some(KnownFunction::Final) => facts::DecoratorKind::TypingFinal,
                            Some(KnownFunction::DataclassTransform) => {
                                facts::DecoratorKind::DataclassTransform
                            }
                            _ => facts::DecoratorKind::Other,
                        }
                    }
                    Type::ClassLiteral(class) => {
                        definition = self.class_reference(class).map(|class| class.definition);
                        match class.known(self.db) {
                            Some(KnownClass::Staticmethod) => facts::DecoratorKind::StaticMethod,
                            Some(KnownClass::Classmethod) => facts::DecoratorKind::ClassMethod,
                            Some(KnownClass::Property) => facts::DecoratorKind::Property,
                            _ if definition.as_ref().is_some_and(|definition| {
                                definition.module.module_name == "functools"
                                    && definition.lexical_qualname == "cached_property"
                            }) =>
                            {
                                facts::DecoratorKind::StdlibCachedProperty
                            }
                            _ => facts::DecoratorKind::Other,
                        }
                    }
                    _ => facts::DecoratorKind::Unknown,
                };
                let source_digest = match callee_ty {
                    Type::FunctionLiteral(function) => Some(facts::Fingerprint::digest(
                        source_text(self.db, function.definition(self.db).file(self.db)).as_bytes(),
                    )),
                    Type::ClassLiteral(class) => {
                        self.class_reference(class).map(|class| class.source_digest)
                    }
                    _ => None,
                };
                let mut arguments = BTreeMap::new();
                if let Type::DataclassDecorator(params) = result {
                    for (name, flag) in super::DATACLASS_FLAGS {
                        arguments.insert(
                            (*name).into(),
                            facts::LiteralValue::Bool(params.flags(self.db).contains(*flag)),
                        );
                    }
                }
                let mut uncertain = matches!(
                    kind,
                    facts::DecoratorKind::Other
                        | facts::DecoratorKind::Unknown
                        | facts::DecoratorKind::DataclassTransform
                );
                if kind == facts::DecoratorKind::StdlibDataclass
                    && let ast::Expr::Call(call) = &decorator.expression
                {
                    let bound_arguments =
                        CallArguments::from_arguments_typed(&call.arguments, |expression| {
                            expression
                                .inferred_type(&self.model)
                                .unwrap_or_else(Type::unknown)
                        });
                    let resolved_options = callee_ty
                        .try_call(self.db, &self.env, &bound_arguments)
                        .ok()
                        .is_some_and(|bindings| {
                            let mut overloads = bindings
                                .iter_flat()
                                .flat_map(|binding| {
                                    binding.matching_overloads().map(|(_, overload)| overload)
                                })
                                .peekable();
                            overloads.peek().is_some()
                                && overloads.all(|overload| {
                                    super::DATACLASS_FLAGS.iter().all(|(name, _)| {
                                        overload
                                            .parameter_type_by_name(self.db, name, true)
                                            .ok()
                                            .flatten()
                                            .is_some_and(|ty| {
                                                matches!(
                                                    ty.as_literal_value_kind(),
                                                    Some(LiteralValueTypeKind::Bool(_))
                                                )
                                            })
                                    })
                                })
                        });
                    if !resolved_options {
                        uncertain = true;
                        arguments.clear();
                    }
                }
                facts::DecoratorFact {
                    kind,
                    expression_range: source_range(decorator.expression.range()),
                    definition,
                    source_digest,
                    arguments,
                    uncertainty: if uncertain {
                        BTreeSet::from([facts::UncertaintyReason::DynamicDecorator])
                    } else {
                        BTreeSet::new()
                    },
                }
            })
            .collect()
    }

    fn globals(&mut self, file: ProgramFile<'db>) {
        let scope = ty_python_core::global_scope(self.db, file);
        let mut globals = BTreeMap::new();
        for member in all_end_of_scope_members(self.db, scope) {
            let ty = self.value_type(member.member.ty);
            globals
                .entry(member.member.name.to_string())
                .or_insert_with(|| facts::GlobalBindingFact {
                    name: member.member.name.to_string(),
                    mutability: if self.module.source_dialect == facts::SourceDialect::SoacStrict {
                        facts::GlobalMutability::FinalAfterSeal
                    } else {
                        facts::GlobalMutability::Unknown
                    },
                    uncertainty: uncertainty(&ty),
                    value_type: ty,
                    definition: self.definition(member.first_reachable_definition),
                });
        }
        self.module.global_bindings = globals.into_values().collect();
    }

    fn function(&mut self, node: &ast::StmtFunctionDef) -> Option<facts::SourceIdentity> {
        let definition = node.definition(&self.model);
        let identity = self.definition(definition)?;
        let function = infer_definition_types(self.db, definition).function_type(definition);
        let mut signature = function
            .map(|function| self.signature(&function.last_definition_signature(self.db), 0))
            .unwrap_or_else(unknown_signature);
        let decorators = self.decorators(&node.decorator_list);
        let mut function_uncertainty = signature.uncertainty.clone();
        function_uncertainty.extend(
            decorators
                .iter()
                .flat_map(|decorator| decorator.uncertainty.iter().copied()),
        );
        let index = semantic_index(self.db, definition.program_file(self.db));
        let generator = index.scope_ids().any(|scope| {
            scope.node(self.db).as_function().is_some_and(|function| {
                let parsed = parsed_module(self.db, definition.python_file(self.db)).load(self.db);
                function.node(&parsed).range() == node.range()
            }) && scope.file_scope_id(self.db).is_generator_function(index)
        });
        let function_kind = match (node.is_async, generator) {
            (false, false) => facts::FunctionKind::Synchronous,
            (true, false) => facts::FunctionKind::Coroutine,
            (false, true) => facts::FunctionKind::Generator,
            (true, true) => facts::FunctionKind::AsyncGenerator,
        };
        if function_kind != facts::FunctionKind::Synchronous {
            // The schema does not turn an annotated generator element or async
            // body result into a synchronous checked return contract.
            signature
                .uncertainty
                .insert(facts::UncertaintyReason::UnsupportedType);
        }
        let mut nominal_bindings = Vec::new();
        for (index, parameter) in node.parameters.iter().enumerate() {
            if let Some(annotation) = parameter.annotation()
                && let Some(parameter_type) = signature.parameters.get(index)
                && parameter_type.annotation_origin == facts::AnnotationOrigin::Explicit
            {
                self.nominal_annotation_leaves(
                    &self.model,
                    &facts::NominalBindingOwner::Function {
                        function: identity.clone(),
                        annotation: facts::AnnotationTarget::Parameter {
                            index: u32::try_from(index).ok()?,
                        },
                    },
                    annotation,
                    &parameter_type.value_type,
                    &mut nominal_bindings,
                );
            }
        }
        if let Some(annotation) = node.returns.as_deref()
            && signature.return_annotation_origin == facts::AnnotationOrigin::Explicit
        {
            self.nominal_annotation_leaves(
                &self.model,
                &facts::NominalBindingOwner::Function {
                    function: identity.clone(),
                    annotation: facts::AnnotationTarget::Return,
                },
                annotation,
                &signature.return_type,
                &mut nominal_bindings,
            );
        }
        self.module.nominal_bindings.extend(nominal_bindings);
        self.module.functions.push(facts::FunctionTypeFact {
            identity: identity.clone(),
            function_kind,
            signature,
            decorators,
            uncertainty: function_uncertainty,
        });
        Some(identity)
    }

    /// The signature and each leaf's type come from real checker inference;
    /// syntax only identifies the value-use paths the runtime can consume
    /// without evaluating annotations. In particular, a spelling like
    /// Optional is not enough: its actual semantic special-form identity is
    /// required before traversing its slice.
    fn nominal_annotation_leaves(
        &self,
        model: &SemanticModel<'db>,
        owner: &facts::NominalBindingOwner,
        expression: &ast::Expr,
        contract: &facts::StaticType,
        output: &mut Vec<facts::NominalBindingFact>,
    ) {
        let mut pending = Vec::new();
        // A normalized class set cannot tell us that one alias was omitted.
        // Publish all required leaves for this annotation owner, or none, so
        // an unresolved alias never borrows another leaf's actual target.
        if self.visit_nominal_annotation_leaves(model, owner, expression, contract, &mut pending) {
            output.extend(pending);
        }
    }

    fn visit_nominal_annotation_leaves(
        &self,
        model: &SemanticModel<'db>,
        owner: &facts::NominalBindingOwner,
        expression: &ast::Expr,
        contract: &facts::StaticType,
        output: &mut Vec<facts::NominalBindingFact>,
    ) -> bool {
        if !contract.has_supported_boundary_shape() {
            return false;
        }
        if matches!(expression, ast::Expr::NoneLiteral(_))
            || self.is_builtin_annotation_leaf(model, expression)
        {
            return true;
        }
        match expression {
            ast::Expr::Name(name) => {
                let Some(binding) = self.nominal_name_binding(model, owner, name, contract) else {
                    return false;
                };
                output.push(binding);
                true
            }
            ast::Expr::BinOp(binary) if binary.op == ast::Operator::BitOr => {
                let left = self.visit_nominal_annotation_leaves(
                    model,
                    owner,
                    &binary.left,
                    contract,
                    output,
                );
                let right = self.visit_nominal_annotation_leaves(
                    model,
                    owner,
                    &binary.right,
                    contract,
                    output,
                );
                left && right
            }
            ast::Expr::Subscript(subscript)
                if matches!(
                    subscript.value.inferred_type(model),
                    Some(Type::SpecialForm(
                        super::SpecialFormType::Optional | super::SpecialFormType::Union
                    ))
                ) =>
            {
                if let ast::Expr::Tuple(tuple) = subscript.slice.as_ref() {
                    let mut complete = true;
                    for element in &tuple.elts {
                        complete &= self.visit_nominal_annotation_leaves(
                            model, owner, element, contract, output,
                        );
                    }
                    complete
                } else {
                    self.visit_nominal_annotation_leaves(
                        model,
                        owner,
                        &subscript.slice,
                        contract,
                        output,
                    )
                }
            }
            ast::Expr::Subscript(subscript) => {
                if matches!(subscript.value.inferred_type(model),
                    Some(Type::ClassLiteral(class)) if class.known(self.db) == Some(KnownClass::Type))
                {
                    // The supported logical contract for type[T] checks the
                    // value as a type object, not as an instance of T.
                    return true;
                }
                let Some(Type::SpecialForm(form)) = subscript.value.inferred_type(model) else {
                    return false;
                };
                match form {
                    super::SpecialFormType::Type => true,
                    super::SpecialFormType::Annotated => {
                        // Metadata is not part of the declared value type and
                        // must not introduce extra required nominal targets.
                        if let ast::Expr::Tuple(tuple) = subscript.slice.as_ref()
                            && let Some(value) = tuple.elts.first()
                        {
                            self.visit_nominal_annotation_leaves(
                                model, owner, value, contract, output,
                            )
                        } else {
                            false
                        }
                    }
                    super::SpecialFormType::TypeQualifier(
                        super::TypeQualifier::Final
                        | super::TypeQualifier::ClassVar
                        | super::TypeQualifier::InitVar,
                    ) if matches!(owner, facts::NominalBindingOwner::Field { .. }) => self
                        .visit_nominal_annotation_leaves(
                            model,
                            owner,
                            &subscript.slice,
                            contract,
                            output,
                        ),
                    _ => false,
                }
            }
            ast::Expr::StringLiteral(string) => {
                // This is the checker's existing forward-annotation parse and
                // scope witness, not another annotation parser. Its submodel
                // is required for both type and definition queries on these
                // nodes, which are not in the module's ordinary AST.
                if let Some((parsed, annotation_model)) = model.enter_string_annotation(string) {
                    self.visit_nominal_annotation_leaves(
                        &annotation_model,
                        owner,
                        parsed.expr(),
                        contract,
                        output,
                    )
                } else {
                    false
                }
            }
            // Attribute access, type aliases, and arbitrary expressions need
            // a separate explicit operand plan. Never evaluate them or guess
            // an actual runtime object from a source identity.
            _ => false,
        }
    }

    fn is_builtin_annotation_leaf(
        &self,
        model: &SemanticModel<'db>,
        expression: &ast::Expr,
    ) -> bool {
        let Some(ty) = expression.inferred_type(model) else {
            return false;
        };
        self.is_builtin_annotation_type(ty)
    }

    fn is_builtin_annotation_type(&self, ty: Type<'db>) -> bool {
        fn builtins_only(value: &facts::StaticType) -> bool {
            match value {
                facts::StaticType::None
                | facts::StaticType::ExactBuiltin(_)
                | facts::StaticType::NominalBuiltin { .. }
                | facts::StaticType::NumericWidening { .. } => true,
                facts::StaticType::Union(elements) => elements.iter().all(builtins_only),
                facts::StaticType::Optional(element) => builtins_only(element),
                _ => false,
            }
        }
        if let Type::Union(union) = ty {
            return union
                .elements(self.db)
                .iter()
                .all(|ty| self.is_builtin_annotation_type(*ty));
        }
        let instance = match ty {
            // Type-expression inference can already project a class name to
            // its instance type. Ordinary value expressions still require the
            // class-object projection below.
            Type::NominalInstance(_) => ty,
            _ => {
                let Some(instance) = ty.to_instance_approximation(self.db, &self.env) else {
                    return false;
                };
                instance
            }
        };
        builtins_only(&self.value_type(instance))
    }

    fn nominal_name_binding(
        &self,
        model: &SemanticModel<'db>,
        owner: &facts::NominalBindingOwner,
        name: &ast::ExprName,
        contract: &facts::StaticType,
    ) -> Option<facts::NominalBindingFact> {
        fn contains(contract: &facts::StaticType, class: &facts::ClassReference) -> bool {
            match contract {
                facts::StaticType::NominalClass(reference)
                | facts::StaticType::ExactClass(reference) => reference == class,
                facts::StaticType::Union(elements) => {
                    elements.iter().any(|element| contains(element, class))
                }
                facts::StaticType::Optional(element) => contains(element, class),
                _ => false,
            }
        }
        let class = match name.inferred_type(model)? {
            Type::ClassLiteral(class) => self.class_reference(class)?,
            Type::NominalInstance(instance) => {
                self.class_reference(instance.class_literal(self.db, &self.env))?
            }
            _ => return None,
        };
        if !contains(contract, &class) {
            return None;
        }
        // Unlike an IDE's first-definition shortcut, all reachable definitions
        // must agree on one actual local binding. Preserve every explicit
        // import, including plain `from module import Class`: IDE alias
        // preservation only retains `as` clauses. The runtime must read the
        // actual local binding, not the imported class's source definition.
        let definitions = definitions_for_name(
            model,
            name.id.as_str(),
            name.into(),
            ImportAliasResolution::PreserveImports,
        );
        let [resolved] = definitions.as_slice() else {
            return None;
        };
        let definition = resolved.definition()?;
        if definition.program_file(self.db) != self.model.program_file()
            || matches!(definition.kind(self.db), DefinitionKind::StarImport(_))
        {
            return None;
        }
        let binding = self.definition(definition)?;
        if !matches!(
            binding.definition_kind,
            facts::DefinitionKind::Class | facts::DefinitionKind::Assignment
        ) {
            return None;
        }
        let scope = definition.scope(self.db);
        let index = semantic_index(self.db, scope.program_file(self.db));
        let binding_scope = match scope.node(self.db) {
            NodeWithScopeKind::Module => self.module.module_body_identity(),
            NodeWithScopeKind::Class(node) => {
                self.definition(index.expect_single_definition(node))?
            }
            NodeWithScopeKind::Function(node) => {
                self.definition(index.expect_single_definition(node))?
            }
            _ => return None,
        };
        Some(facts::NominalBindingFact {
            owner: owner.clone(),
            expression_range: source_range(name.range()),
            name: name.id.to_string(),
            class,
            binding,
            binding_scope,
        })
    }

    fn descriptor(&self, ty: Type<'db>) -> facts::DescriptorFact {
        if let Type::PropertyInstance(property) = ty {
            let implementation = |ty: Option<Type<'db>>| {
                ty.and_then(|ty| ty.as_function_literal())
                    .and_then(|function| self.definition(function.definition(self.db)))
            };
            return facts::DescriptorFact {
                kind: facts::DescriptorKind::Property,
                descriptor_type: Some(Box::new(unsupported(facts::UnsupportedTypeKind::Other))),
                getter: implementation(property.getter(self.db)),
                setter: implementation(property.setter(self.db)),
                deleter: implementation(property.deleter(self.db)),
            };
        }
        if matches!(ty, Type::FunctionLiteral(_) | Type::BoundMethod(_)) {
            return facts::DescriptorFact::default();
        }
        let Some(class) = ty.nominal_class(self.db, &self.env) else {
            return if ty.is_dynamic() {
                facts::DescriptorFact {
                    kind: facts::DescriptorKind::Unknown,
                    ..Default::default()
                }
            } else {
                facts::DescriptorFact::default()
            };
        };
        let has = |name| {
            ty.class_member(self.db, &self.env, name)
                .place
                .ignore_possibly_undefined()
                .is_some()
        };
        if !has("__get__") {
            return facts::DescriptorFact::default();
        }
        let reference = self.class_reference(class.class_literal(self.db));
        let cached = reference.as_ref().is_some_and(|reference| {
            reference.definition.module.module_name == "functools"
                && reference.definition.lexical_qualname == "cached_property"
        });
        facts::DescriptorFact {
            kind: if cached {
                facts::DescriptorKind::StdlibCachedProperty
            } else if has("__set__") || has("__delete__") {
                facts::DescriptorKind::Data
            } else {
                facts::DescriptorKind::NonData
            },
            descriptor_type: Some(Box::new(self.value_type(ty))),
            ..Default::default()
        }
    }

    fn class(&mut self, node: &ast::StmtClassDef) -> Option<facts::SourceIdentity> {
        let db = self.db;
        let definition = node.definition(&self.model);
        let identity = self.definition(definition)?;
        let class = original_class_type(db, definition)?.as_static()?;
        let own_reference = self.class_reference(class.into())?;
        let instance = Type::instance(db, &self.env, class.default_specialization(db));
        let decorators = self.decorators(&node.decorator_list);
        let mut reasons = BTreeSet::new();
        let mut class_uncertainty = BTreeSet::new();
        if decorators.iter().any(|decorator| {
            !decorator.uncertainty.is_empty()
                || !matches!(
                    decorator.kind,
                    facts::DecoratorKind::StdlibDataclass | facts::DecoratorKind::TypingFinal
                )
        }) {
            reasons.insert(facts::DynamicClassReason::UnknownDecorator);
            class_uncertainty.insert(facts::UncertaintyReason::DynamicDecorator);
        }
        if self.module.source_dialect != facts::SourceDialect::SoacStrict {
            reasons.insert(facts::DynamicClassReason::UnresolvedAnalysis);
        }
        let metaclass_ty = class.metaclass(db);
        let metaclass = match metaclass_ty {
            Type::ClassLiteral(meta) if meta.known(db) == Some(KnownClass::Type) => {
                facts::MetaclassFact::BuiltinType
            }
            Type::ClassLiteral(meta) => self
                .class_reference(meta)
                .map(facts::MetaclassFact::Class)
                .unwrap_or(facts::MetaclassFact::Dynamic),
            _ => facts::MetaclassFact::Dynamic,
        };
        if metaclass != facts::MetaclassFact::BuiltinType {
            reasons.insert(facts::DynamicClassReason::NonParticipatingMetaclass);
            class_uncertainty.insert(facts::UncertaintyReason::DynamicMetaclass);
        }
        let mut complete = class.try_mro(db, None).is_ok();
        let mut linearized_bases = Vec::new();
        for base in class.iter_mro(db, None).skip(1) {
            if let ClassBase::Class(base) = base {
                if let Some(reference) = self.base_reference(base.class_literal(db)) {
                    if self.resolve_external_bases
                        && base.known(db) != Some(KnownClass::Object)
                        && base.class_literal(db).as_static().is_none_or(|base| {
                            base.file(db) != self.model.program_file().file(db)
                                && !external_strict_base_is_candidate(db, base)
                        })
                    {
                        reasons.insert(facts::DynamicClassReason::MutableBase);
                    }
                    linearized_bases.push(reference);
                } else {
                    complete = false;
                }
            } else {
                complete = false;
            }
        }
        let mut bases = Vec::new();
        for base in class.explicit_bases(db) {
            if let Some(reference) = base
                .to_class_type(db)
                .and_then(|base| self.base_reference(base.class_literal(db)))
            {
                bases.push(reference);
            } else {
                complete = false;
            }
        }
        if !complete {
            reasons.insert(facts::DynamicClassReason::UnknownBase);
        }
        // Instance attribute hooks can bypass the proposed storage semantics.
        // Construction callbacks (__init_subclass__/__set_name__) instead run
        // after native pre-callback policy installation; their source presence
        // alone is not a reason to exclude a class. This remains only a proposal:
        // runtime admission must authenticate bases, callbacks and namespaces.
        for name in [
            "__getattribute__",
            "__getattr__",
            "__setattr__",
            "__delattr__",
        ] {
            if let Some(ty) = instance
                .class_member(db, &self.env, name)
                .place
                .ignore_possibly_undefined()
            {
                if let Some(function) = ty.as_function_literal() {
                    if self
                        .definition(function.definition(db))
                        .is_none_or(|identity| identity.module.module_name != "builtins")
                    {
                        reasons.insert(facts::DynamicClassReason::CustomAttributeHooks);
                    }
                } else if !matches!(ty, Type::Callable(_)) {
                    reasons.insert(facts::DynamicClassReason::CustomAttributeHooks);
                }
            }
        }
        let generator = CodeGeneratorKind::from_class(db, class.into());
        let stdlib_dataclass = decorators
            .iter()
            .any(|decorator| decorator.kind == facts::DecoratorKind::StdlibDataclass);
        let uncertain_dataclass_options = decorators.iter().any(|decorator| {
            decorator.kind == facts::DecoratorKind::StdlibDataclass
                && !decorator.uncertainty.is_empty()
        });
        let mut transform = generator
            .filter(|_| !uncertain_dataclass_options)
            .map(|generator| {
                let kind = if stdlib_dataclass {
                    facts::TransformKind::StdlibDataclass
                } else if matches!(generator, CodeGeneratorKind::DataclassLike(_)) {
                    facts::TransformKind::DataclassTransform
                } else {
                    facts::TransformKind::UnsupportedFramework
                };
                if kind != facts::TransformKind::StdlibDataclass
                    || self.module.language_policy.adapters.dataclasses
                        == facts::StdlibDataclassPolicy::Dynamic
                {
                    reasons.insert(facts::DynamicClassReason::FrameworkManaged);
                }
                let options = class.dataclass_params(db).map(|params| {
                    let flags = params.flags(db);
                    facts::DataclassOptions {
                        init: flags.contains(DataclassFlags::INIT),
                        repr: flags.contains(DataclassFlags::REPR),
                        eq: flags.contains(DataclassFlags::EQ),
                        order: flags.contains(DataclassFlags::ORDER),
                        unsafe_hash: flags.contains(DataclassFlags::UNSAFE_HASH),
                        frozen: flags.contains(DataclassFlags::FROZEN),
                        match_args: flags.contains(DataclassFlags::MATCH_ARGS),
                        kw_only: flags.contains(DataclassFlags::KW_ONLY),
                        slots: flags.contains(DataclassFlags::SLOTS),
                        weakref_slot: flags.contains(DataclassFlags::WEAKREF_SLOT),
                    }
                });
                facts::ClassTransformFact {
                    kind,
                    provenance: decorators
                        .iter()
                        .find(|decorator| decorator.kind == facts::DecoratorKind::StdlibDataclass)
                        .and_then(|decorator| decorator.definition.clone()),
                    dataclass_options: options,
                    generated_methods: BTreeSet::new(),
                }
            });
        let generated_init = transform.is_some()
            && super::member::class_member(db, class.body_scope(db), "__init__").is_undefined()
            && class
                .own_synthesized_member(db, &self.env, None, None, "__init__")
                .is_some();
        let mut fields = Vec::new();
        let mut field_bindings = Vec::new();
        if let Some(generator) = generator {
            for (name, field) in class.fields(db, None, generator) {
                let value_type = self.value_type(field.declared_ty);
                let (init_only, default_ty, initialized) = match &field.kind {
                    TyFieldKind::Dataclass {
                        init_only,
                        default_ty,
                        init,
                        ..
                    } => (*init_only, *default_ty, *init),
                    TyFieldKind::Pydantic {
                        default_ty, init, ..
                    } => (false, *default_ty, *init),
                    TyFieldKind::NamedTuple { default_ty } => (false, *default_ty, true),
                    _ => (false, None, false),
                };
                let declaring_class = field
                    .first_declaration
                    .and_then(|definition| self.class_for_scope(definition.scope(db)))
                    .unwrap_or_else(|| own_reference.clone());
                let default = self.field_default(field.first_declaration, default_ty);
                let exported = facts::FieldTypeFact {
                    name: name.to_string(),
                    declaring_class,
                    uncertainty: uncertainty(&value_type),
                    value_type,
                    annotation_origin: self.field_annotation_origin(field.first_declaration),
                    annotation_definition: self
                        .field_annotation_definition(field.first_declaration),
                    field_kind: if init_only {
                        facts::FieldKind::InitOnly
                    } else {
                        facts::FieldKind::InstanceField
                    },
                    read_policy: facts::FieldReadPolicy::PythonAttribute,
                    write_policy: if init_only {
                        facts::FieldWritePolicy::InitOnly
                    } else {
                        facts::FieldWritePolicy::DeclaredField
                    },
                    initialization: if initialized && generated_init && !init_only {
                        facts::InitializationPolicy::InitializedByConstructor
                    } else {
                        facts::InitializationPolicy::MayBeAbsent
                    },
                    default,
                    descriptor: facts::DescriptorFact::default(),
                };
                self.field_nominal_bindings(
                    &exported,
                    field.first_declaration,
                    &own_reference,
                    &mut field_bindings,
                );
                fields.push(exported);
            }
        }
        let mut field_names: BTreeSet<String> =
            fields.iter().map(|field| field.name.clone()).collect();
        for (name, qualifiers, declaration) in class.own_annotated_qualifiers(db) {
            let declared = super::inferred_declaration(db, declaration);
            // The generator's field query already removes KW_ONLY markers.
            // Do not reintroduce one from the annotation-history append pass,
            // including when no generated constructor exists. Only the actual
            // dataclass-like role and semantic sentinel identity authorize this
            // exclusion; ordinary annotations and namesakes remain real fields.
            if generator.is_some_and(|generator| generator.is_dataclass_like())
                && declared.declared().is_some_and(|declared| {
                    declared.inner_type().is_instance_of(db, KnownClass::KwOnly)
                })
            {
                continue;
            }
            let name = name.to_string();
            if !field_names.insert(name.clone()) {
                continue;
            }
            let value_type = declared
                .declared()
                .map(|declared| self.value_type(declared.inner_type()))
                .unwrap_or(facts::StaticType::Unknown);
            let classvar = qualifiers.contains(TypeQualifiers::CLASS_VAR);
            let init_only = qualifiers.contains(TypeQualifiers::INIT_VAR);
            let callable = matches!(value_type, facts::StaticType::Callable(_));
            let default = self.field_default(Some(declaration), None);
            let has_default = !matches!(default, facts::DefaultFact::Missing);
            let descriptor = instance
                .class_member(db, &self.env, &name)
                .place
                .ignore_possibly_undefined()
                .map(|ty| self.descriptor(ty))
                .unwrap_or_default();
            if !matches!(descriptor.kind, facts::DescriptorKind::None) {
                reasons.insert(facts::DynamicClassReason::UnsupportedDescriptor);
            }
            let exported = facts::FieldTypeFact {
                name,
                declaring_class: own_reference.clone(),
                uncertainty: uncertainty(&value_type),
                value_type,
                annotation_origin: self.field_annotation_origin(Some(declaration)),
                annotation_definition: self.field_annotation_definition(Some(declaration)),
                field_kind: if classvar {
                    facts::FieldKind::ClassVariable
                } else if init_only {
                    facts::FieldKind::InitOnly
                } else if callable {
                    facts::FieldKind::CallableInstanceField
                } else if has_default {
                    facts::FieldKind::ShadowableClassDefault
                } else {
                    facts::FieldKind::InstanceField
                },
                read_policy: if has_default {
                    facts::FieldReadPolicy::InstanceThenClassDefault
                } else {
                    facts::FieldReadPolicy::PythonAttribute
                },
                write_policy: if classvar {
                    facts::FieldWritePolicy::ClassVariableRejected
                } else if init_only {
                    facts::FieldWritePolicy::InitOnly
                } else {
                    facts::FieldWritePolicy::DeclaredField
                },
                initialization: facts::InitializationPolicy::MayBeAbsent,
                default,
                descriptor,
            };
            self.field_nominal_bindings(
                &exported,
                Some(declaration),
                &own_reference,
                &mut field_bindings,
            );
            fields.push(exported);
        }
        // Enumerate implicit names from the semantic index, then ask the same
        // instance-member query used for Python attribute checking for each type.
        let index = semantic_index(db, class.program_file(db));
        let mut implicit = BTreeSet::new();
        for scope in ty_python_core::attribute_scopes(db, class.body_scope(db)) {
            implicit.extend(
                index
                    .place_table(scope)
                    .members()
                    .filter_map(|member| member.as_instance_attribute().map(str::to_owned)),
            );
        }
        for name in implicit {
            if !field_names.insert(name.clone()) {
                continue;
            }
            let Place::Defined(place) = instance.instance_member(db, &self.env, &name).place else {
                continue;
            };
            let value_type = self.value_type(place.ty);
            let provenance = place.provenance.definition();
            let declaring_class = provenance
                .and_then(|definition| self.enclosing_class_for_scope(definition.scope(db)))
                .unwrap_or_else(|| own_reference.clone());
            let declaration = self.unique_implicit_annotation(provenance, &name);
            let exported = facts::FieldTypeFact {
                name,
                declaring_class,
                field_kind: if matches!(value_type, facts::StaticType::Callable(_)) {
                    facts::FieldKind::CallableInstanceField
                } else {
                    facts::FieldKind::InstanceField
                },
                uncertainty: uncertainty(&value_type),
                value_type,
                annotation_origin: match place.origin {
                    TypeOrigin::Declared => facts::AnnotationOrigin::Explicit,
                    TypeOrigin::Inferred => facts::AnnotationOrigin::Inferred,
                },
                annotation_definition: self.field_annotation_definition(declaration),
                read_policy: facts::FieldReadPolicy::PythonAttribute,
                write_policy: facts::FieldWritePolicy::DeclaredField,
                initialization: facts::InitializationPolicy::MayBeAbsent,
                default: facts::DefaultFact::Missing,
                descriptor: facts::DescriptorFact::default(),
            };
            self.field_nominal_bindings(
                &exported,
                declaration,
                &own_reference,
                &mut field_bindings,
            );
            fields.push(exported);
        }
        let mut methods = BTreeMap::new();
        let mut class_members = BTreeMap::new();
        let class_places = place_table(db, class.body_scope(db));
        for member in all_end_of_scope_members(db, class.body_scope(db)) {
            // A class body can write a global or nonlocal cell, but that does not
            // install a binding in its prepared namespace. The scope iterator
            // includes those writes for flow analysis; they are not members.
            if class_places
                .symbol_by_name(member.member.name.as_str())
                .is_some_and(|symbol| symbol.is_global() || symbol.is_nonlocal())
            {
                continue;
            }
            let name = member.member.name.to_string();
            let ty = member.member.ty;
            let function = ty.as_function_literal().or_else(|| {
                if let Type::PropertyInstance(property) = ty {
                    property.getter(db).and_then(Type::as_function_literal)
                } else {
                    None
                }
            });
            if let Some(function) = function {
                let signature = self.signature(&function.last_definition_signature(db), 0);
                let declared_final = function.has_known_decorator(db, FunctionDecorators::FINAL);
                let binding = if matches!(ty, Type::PropertyInstance(_)) {
                    facts::MethodBinding::PropertyGetter
                } else if function.is_staticmethod(db) {
                    facts::MethodBinding::Static
                } else if function.is_classmethod(db) {
                    facts::MethodBinding::Class
                } else {
                    facts::MethodBinding::Instance
                };
                methods
                    .entry(name.clone())
                    .or_insert(facts::MethodTypeFact {
                        name,
                        declaring_class: own_reference.clone(),
                        binding,
                        uncertainty: signature.uncertainty.clone(),
                        signature,
                        declared_final,
                        override_policy: if declared_final {
                            facts::OverridePolicy::DeclaredFinal
                        } else {
                            facts::OverridePolicy::CompatibleSignatureRequired
                        },
                        implementation: self.definition(function.last_definition(db)),
                        generated: None,
                    });
            } else {
                let value_type = self.value_type(ty);
                let descriptor = self.descriptor(ty);
                if descriptor.kind != facts::DescriptorKind::None {
                    reasons.insert(facts::DynamicClassReason::UnsupportedDescriptor);
                }
                class_members
                    .entry(name.clone())
                    .or_insert(facts::ClassMemberFact {
                        name,
                        kind: if descriptor.kind != facts::DescriptorKind::None {
                            facts::ClassMemberKind::Descriptor
                        } else if matches!(ty, Type::ClassLiteral(_)) {
                            facts::ClassMemberKind::NestedClass
                        } else {
                            facts::ClassMemberKind::ShadowableDefault
                        },
                        uncertainty: uncertainty(&value_type),
                        value_type,
                        definition: self.definition(member.first_reachable_definition),
                        descriptor,
                    });
            }
        }
        if let Some(transform) = &mut transform {
            let body_scope = class.body_scope(db);
            let body_places = place_table(db, body_scope);
            let body_use_def = use_def_map(db, body_scope);
            for name in [
                "__init__",
                "__repr__",
                "__eq__",
                "__ne__",
                "__lt__",
                "__le__",
                "__gt__",
                "__ge__",
                "__hash__",
                "__setattr__",
                "__delattr__",
                "__replace__",
            ] {
                // The ordinary member query tries the actual own binding before
                // synthesis. Preserve that precedence here too, including lambdas
                // and non-function assignments. An annotation alone is not a
                // runtime binding and does not suppress dataclass generation.
                let has_own_binding = body_places.symbol_id(name).is_some_and(|symbol| {
                    place_from_bindings(
                        db,
                        &self.env,
                        body_use_def.end_of_scope_symbol_bindings(symbol),
                    )
                    .place
                    .ignore_possibly_undefined()
                    .is_some()
                });
                if has_own_binding {
                    continue;
                }
                if let Some(ty) = class.own_synthesized_member(db, &self.env, None, None, name)
                    && ty.try_upcast_to_callable(db, &self.env).is_some()
                {
                    let signature = self.callable_signature(ty, 0);
                    transform.generated_methods.insert(name.into());
                    methods.insert(
                        name.into(),
                        facts::MethodTypeFact {
                            name: name.into(),
                            declaring_class: own_reference.clone(),
                            binding: facts::MethodBinding::Instance,
                            uncertainty: signature.uncertainty.clone(),
                            signature,
                            declared_final: false,
                            override_policy: facts::OverridePolicy::CompatibleSignatureRequired,
                            implementation: None,
                            generated: Some(facts::GeneratedFunctionFact {
                                class: own_reference.clone(),
                                transform: transform.kind,
                                name: name.into(),
                            }),
                        },
                    );
                }
            }
        }
        let slots = instance
            .class_member(db, &self.env, "__slots__")
            .place
            .ignore_possibly_undefined()
            .is_some();
        let openness = if class.is_final(db) {
            facts::ClassOpenness::DeclaredFinal
        } else {
            facts::ClassOpenness::OpenSubclassFamily
        };
        class_uncertainty.insert(facts::UncertaintyReason::OpenWorld);
        self.module.nominal_bindings.extend(field_bindings);
        self.module.classes.push(facts::ClassTypeFact {
            identity: identity.clone(),
            bases,
            metaclass,
            decorators,
            participation: if reasons.is_empty() {
                facts::ParticipationProposal::Candidate
            } else {
                facts::ParticipationProposal::Dynamic(reasons)
            },
            dictionary: if uncertain_dataclass_options
                || class_uncertainty.contains(&facts::UncertaintyReason::DynamicDecorator)
                || class_uncertainty.contains(&facts::UncertaintyReason::DynamicMetaclass)
            {
                facts::ClassDictionarySemantics::Unknown
            } else if slots {
                facts::ClassDictionarySemantics::ExplicitSlots
            } else {
                facts::ClassDictionarySemantics::DictionaryBearing
            },
            instance_fields: fields,
            methods: methods.into_values().collect(),
            class_members: class_members.into_values().collect(),
            inheritance: facts::InheritanceFact {
                linearized_bases,
                complete,
            },
            openness,
            transform,
            uncertainty: class_uncertainty,
        });
        Some(identity)
    }

    fn class_for_scope(&self, scope: ScopeId<'db>) -> Option<facts::ClassReference> {
        let index = semantic_index(self.db, scope.program_file(self.db));
        let class = scope.node(self.db).as_class()?;
        let definition = index.expect_single_definition(class);
        self.class_reference(original_class_type(self.db, definition)?)
    }

    fn enclosing_class_scope(&self, mut scope: ScopeId<'db>) -> Option<ScopeId<'db>> {
        loop {
            if matches!(scope.node(self.db), NodeWithScopeKind::Class(_)) {
                return Some(scope);
            }
            scope = scope
                .scope(self.db)
                .parent()?
                .to_scope_id(self.db, scope.program_file(self.db));
        }
    }

    fn enclosing_class_for_scope(&self, scope: ScopeId<'db>) -> Option<facts::ClassReference> {
        self.class_for_scope(self.enclosing_class_scope(scope)?)
    }

    fn unique_implicit_annotation(
        &self,
        declaration: Option<Definition<'db>>,
        name: &str,
    ) -> Option<Definition<'db>> {
        let declaration = declaration?;
        if !matches!(
            declaration.kind(self.db),
            DefinitionKind::AnnotatedAssignment(_)
        ) {
            return None;
        }
        let scope = declaration.scope(self.db);
        let class_scope = self.enclosing_class_scope(scope)?;
        if scope == class_scope {
            return Some(declaration);
        }
        // Ordinary instance-member inference intentionally chooses the first
        // annotated method. That type is useful, but it does not prove a unique
        // nominal binding source when other methods also annotate this field.
        // Use the real semantic declaration query; do not scan annotation text
        // or manufacture a source identity from the selected display type.
        let mut found = false;
        for (declarations, _) in crate::attribute_declarations(self.db, class_scope, name) {
            for candidate in
                declarations.filter_map(|declaration| declaration.declaration.definition())
            {
                if !matches!(
                    candidate.kind(self.db),
                    DefinitionKind::AnnotatedAssignment(_)
                ) {
                    continue;
                }
                if candidate != declaration {
                    return None;
                }
                found = true;
            }
        }
        found.then_some(declaration)
    }

    fn field_annotation_definition(
        &self,
        declaration: Option<Definition<'db>>,
    ) -> Option<facts::SourceIdentity> {
        let declaration = declaration?;
        matches!(
            declaration.kind(self.db),
            DefinitionKind::AnnotatedAssignment(_)
        )
        .then(|| self.definition(declaration))
        .flatten()
    }

    fn field_nominal_bindings(
        &self,
        field: &facts::FieldTypeFact,
        declaration: Option<Definition<'db>>,
        owning_class: &facts::ClassReference,
        output: &mut Vec<facts::NominalBindingFact>,
    ) {
        // Inherited fields keep their original declaration and binding plan;
        // a child namespace cannot re-authorize the base's actual targets.
        if field.annotation_origin != facts::AnnotationOrigin::Explicit
            || &field.declaring_class != owning_class
        {
            return;
        }
        let Some(reference) = field.annotation_reference() else {
            return;
        };
        let Some(declaration) = declaration else {
            return;
        };
        if declaration.program_file(self.db) != self.model.program_file() {
            return;
        }
        let DefinitionKind::AnnotatedAssignment(assignment) = declaration.kind(self.db) else {
            return;
        };
        let parsed = parsed_module(self.db, declaration.python_file(self.db)).load(self.db);
        self.nominal_annotation_leaves(
            &self.model,
            &facts::NominalBindingOwner::Field { field: reference },
            assignment.annotation(&parsed),
            &field.value_type,
            output,
        );
    }

    fn field_annotation_origin(
        &self,
        declaration: Option<Definition<'db>>,
    ) -> facts::AnnotationOrigin {
        let Some(declaration) = declaration else {
            return facts::AnnotationOrigin::Unresolved;
        };
        let Some(declared) = super::inferred_declaration(self.db, declaration).declared() else {
            return facts::AnnotationOrigin::Unresolved;
        };
        // `Final` without a value annotation still gets its value type from
        // inference. The semantic declaration uses Unknown + FINAL for that
        // case; it must not become a mandatory runtime type contract.
        if declared.qualifiers().contains(TypeQualifiers::FINAL)
            && declared.inner_type().is_unknown()
        {
            return facts::AnnotationOrigin::Inferred;
        }
        match declared.origin() {
            TypeOrigin::Declared => facts::AnnotationOrigin::Explicit,
            TypeOrigin::Inferred => facts::AnnotationOrigin::Inferred,
        }
    }

    fn field_default(
        &self,
        declaration: Option<Definition<'db>>,
        fallback: Option<Type<'db>>,
    ) -> facts::DefaultFact {
        if let Some(declaration) = declaration {
            let parsed = parsed_module(self.db, declaration.python_file(self.db)).load(self.db);
            if let DefinitionKind::AnnotatedAssignment(assignment) = declaration.kind(self.db)
                && let Some(value) = assignment.value(&parsed)
            {
                let model = SemanticModel::new(self.db, declaration.program_file(self.db));
                let ty = value.inferred_type(&model).unwrap_or_else(Type::unknown);
                if let Type::KnownInstance(super::KnownInstanceType::Field(field)) = ty {
                    // This metadata comes from the same successful parameter
                    // binding as ty's dataclass field collector, including
                    // aliases, custom field specifiers and expanded kwargs.
                    let default = fallback.or_else(|| field.default_type(self.db));
                    if let Some(factory) = field.default_factory(self.db) {
                        return facts::DefaultFact::Factory {
                            implementation: factory
                                .as_function_literal()
                                .and_then(|function| self.definition(function.definition(self.db))),
                            return_type: Box::new(
                                default
                                    .map(|ty| self.value_type(ty))
                                    .unwrap_or(facts::StaticType::Unknown),
                            ),
                        };
                    }
                    return default
                        .map(|ty| self.default_value(ty))
                        .unwrap_or(facts::DefaultFact::Missing);
                }
                return self.default_value(ty);
            }
        }
        fallback
            .map(|ty| self.default_value(ty))
            .unwrap_or(facts::DefaultFact::Missing)
    }

    fn attribute(&mut self, node: &ast::ExprAttribute) {
        let receiver = node
            .value
            .inferred_type(&self.model)
            .unwrap_or_else(Type::unknown);
        self.attribute_receivers
            .insert(source_range(node.range()), receiver);
        let receiver_type = self.value_type(receiver);
        let mut reasons = uncertainty(&receiver_type);
        reasons.insert(facts::UncertaintyReason::OpenWorld);
        let class = receiver
            .nominal_class(self.db, &self.env)
            .and_then(|class| self.class_reference(class.class_literal(self.db)));
        let value_type = if node.ctx == ast::ExprContext::Load {
            Some(
                self.value_type(
                    node.inferred_type(&self.model)
                        .unwrap_or_else(Type::unknown),
                ),
            )
        } else {
            None
        };
        self.module.attribute_sites.push(facts::AttributeSiteFact {
            identity: facts::AttributeSiteIdentity {
                module: self.module.module.clone(),
                source_digest: self.module.source_digest,
                enclosing_function: self.owner.clone(),
                expression_range: source_range(node.range()),
            },
            name: node.attr.to_string(),
            access: match node.ctx {
                ast::ExprContext::Load => facts::AttributeAccess::Read,
                ast::ExprContext::Store => facts::AttributeAccess::Write,
                ast::ExprContext::Del => facts::AttributeAccess::Delete,
                _ => facts::AttributeAccess::Read,
            },
            receiver_type,
            value_type,
            declaring_class: class,
            uncertainty: reasons,
        });
    }

    fn call(&mut self, node: &ast::ExprCall) {
        let db = self.db;
        let callable = node
            .func
            .inferred_type(&self.model)
            .unwrap_or_else(Type::unknown);
        let arguments = CallArguments::from_arguments_typed(&node.arguments, |expression| {
            expression
                .inferred_type(&self.model)
                .unwrap_or_else(Type::unknown)
        });
        let bindings = callable.try_call(db, &self.env, &arguments).ok();
        let signature = bindings
            .as_ref()
            .and_then(|bindings| {
                let mut matching = bindings.iter_flat().flat_map(|binding| {
                    binding
                        .matching_overloads()
                        .map(move |(_, overload)| (binding, overload))
                });
                let (binding, only) = matching.next()?;
                if matching.next().is_some() {
                    return None;
                }
                let signature = if let Some(receiver) = binding.bound_type {
                    let typing_self = if let Type::BoundMethod(method) = callable {
                        method.typing_self_type(db)
                    } else {
                        receiver
                    };
                    only.signature.bind_self_with_receiver(
                        db,
                        &self.env,
                        Some(receiver),
                        Some(typing_self),
                    )
                } else {
                    only.signature.clone()
                };
                Some(self.signature(&signature, 0))
            })
            .unwrap_or_else(unknown_signature);
        let mut binding = facts::CallBindingFact::Dynamic;
        let mut call_uncertainty = facts::CallUncertainty::Dynamic;
        let mut targets = Vec::new();
        let mut receiver = None;
        let mut attribute_name = None;
        if let ast::Expr::Attribute(attribute) = &*node.func {
            let ty = attribute
                .value
                .inferred_type(&self.model)
                .unwrap_or_else(Type::unknown);
            let value_type = self.value_type(ty);
            receiver = Some(facts::ReceiverTypeFact {
                uncertainty: uncertainty(&value_type),
                value_type,
            });
            attribute_name = Some(attribute.attr.to_string());
            let instance_field = ty
                .instance_member(db, &self.env, attribute.attr.as_str())
                .place
                .ignore_possibly_undefined()
                .is_some();
            if instance_field && !matches!(callable, Type::BoundMethod(_)) {
                binding = facts::CallBindingFact::CallableInstanceField;
                call_uncertainty = facts::CallUncertainty::CallableInstanceField;
            } else if let Type::BoundMethod(method) = callable {
                let function = method.function(db);
                binding = if function.is_classmethod(db) {
                    facts::CallBindingFact::BoundClassMethod
                } else {
                    facts::CallBindingFact::BoundInstanceMethod
                };
                call_uncertainty = if matches!(ty, Type::ProtocolInstance(_)) {
                    facts::CallUncertainty::StructuralProtocol
                } else {
                    facts::CallUncertainty::OpenSubclassFamily
                };
                if let Some(class) = self.class_for_scope(function.definition(db).scope(db)) {
                    targets.push(facts::CallableTargetFact::Method {
                        class,
                        name: attribute.attr.to_string(),
                        implementation: self.definition(function.definition(db)),
                    });
                }
            } else if let Type::FunctionLiteral(function) = callable {
                binding = if function.is_staticmethod(db) {
                    facts::CallBindingFact::StaticMethod
                } else {
                    facts::CallBindingFact::UnboundFunction
                };
                call_uncertainty = facts::CallUncertainty::OpenSubclassFamily;
                if let Some(identity) = self.definition(function.definition(db)) {
                    targets.push(facts::CallableTargetFact::SourceFunction(identity));
                }
            }
        } else if let Type::FunctionLiteral(function) = callable {
            binding = facts::CallBindingFact::UnboundFunction;
            call_uncertainty = facts::CallUncertainty::ExactStaticTarget;
            if let Some(identity) = self.definition(function.definition(db)) {
                targets.push(facts::CallableTargetFact::SourceFunction(identity));
            }
        }
        let protocol_receiver = receiver.as_ref().is_some_and(|receiver| {
            matches!(
                receiver.value_type,
                facts::StaticType::StructuralProtocol(_)
            )
        });
        if bindings.is_none()
            || receiver.as_ref().is_some_and(|receiver| {
                receiver.value_type.contains_uncertainty() && !protocol_receiver
            })
        {
            call_uncertainty = facts::CallUncertainty::Dynamic;
            binding = facts::CallBindingFact::Dynamic;
            targets.clear();
        }
        if protocol_receiver {
            call_uncertainty = facts::CallUncertainty::StructuralProtocol;
        }
        if targets.is_empty() {
            targets.push(facts::CallableTargetFact::Dynamic);
        }
        self.module.call_sites.push(facts::CallSiteFact {
            identity: facts::CallSiteIdentity {
                module: self.module.module.clone(),
                source_digest: self.module.source_digest,
                enclosing_function: self.owner.clone(),
                expression_range: source_range(node.range()),
                expression_kind: if attribute_name.is_some() {
                    facts::CallExpressionKind::AttributeCall
                } else {
                    facts::CallExpressionKind::Call
                },
            },
            receiver,
            attribute_name,
            candidate_targets: targets,
            binding,
            signature,
            result_type: self.value_type(
                node.inferred_type(&self.model)
                    .unwrap_or_else(Type::unknown),
            ),
            uncertainty: call_uncertainty,
        });
    }
}

impl<'ast> Visitor<'ast> for Exporter<'_> {
    fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
        match statement {
            ast::Stmt::ClassDef(node) => {
                // Bases and decorators execute in the surrounding scope.
                for decorator in &node.decorator_list {
                    self.visit_decorator(decorator);
                }
                if let Some(arguments) = &node.arguments {
                    self.visit_arguments(arguments);
                }
                let previous = self.owner.clone();
                if let Some(owner) = self.class(node) {
                    self.owner = owner;
                }
                self.visit_body(&node.body);
                self.owner = previous;
            }
            ast::Stmt::FunctionDef(node) => {
                for decorator in &node.decorator_list {
                    self.visit_decorator(decorator);
                }
                // Only defaults execute here. Annotation expressions are not
                // runtime call sites under deferred annotations.
                for parameter in node.parameters.iter_non_variadic_params() {
                    if let Some(default) = &parameter.default {
                        self.visit_expr(default);
                    }
                }
                let previous = self.owner.clone();
                if let Some(owner) = self.function(node) {
                    self.owner = owner;
                }
                self.visit_body(&node.body);
                self.owner = previous;
            }
            _ => visitor::walk_stmt(self, statement),
        }
    }

    fn visit_annotation(&mut self, _annotation: &'ast ast::Expr) {}

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        match expression {
            ast::Expr::Call(call) => self.call(call),
            ast::Expr::Attribute(attribute) => self.attribute(attribute),
            ast::Expr::Lambda(lambda) => {
                if let Some(parameters) = &lambda.parameters {
                    for parameter in parameters.iter_non_variadic_params() {
                        if let Some(default) = &parameter.default {
                            self.visit_expr(default);
                        }
                    }
                }
                let program_file = self.model.program_file();
                let index = semantic_index(self.db, program_file);
                let lambda_scope =
                    index.node_scope(ty_python_core::scope::NodeWithScopeRef::Lambda(lambda));
                let enclosing_scope = index
                    .scope(lambda_scope)
                    .parent()
                    .expect("lambda expression has an enclosing semantic scope")
                    .to_scope_id(self.db, program_file);
                let identity = facts::SourceIdentity {
                    module: self.module.module.clone(),
                    lexical_qualname: self.lexical_qualname(enclosing_scope, "<lambda>".into()),
                    source_range: source_range(lambda.range()),
                    definition_kind: facts::DefinitionKind::Lambda,
                };
                let ty = lambda
                    .inferred_type(&self.model)
                    .unwrap_or_else(Type::unknown);
                let signature = self.callable_signature(ty, 0);
                self.module.functions.push(facts::FunctionTypeFact {
                    identity: identity.clone(),
                    function_kind: if lambda_scope.is_generator_function(index) {
                        facts::FunctionKind::Generator
                    } else {
                        facts::FunctionKind::Synchronous
                    },
                    uncertainty: signature.uncertainty.clone(),
                    signature,
                    decorators: Vec::new(),
                });
                let previous = std::mem::replace(&mut self.owner, identity);
                self.visit_expr(&lambda.body);
                self.owner = previous;
                return;
            }
            _ => {}
        }
        visitor::walk_expr(self, expression);
    }
}
