//! Strict-policy diagnostics over ty's resolved symbols, members and callables.
//!
//! These diagnose operations on participating proposals, never establish live
//! runtime protection. Unknown aliases, unsupported frameworks and absent
//! physical-layout promises remain the runtime's responsibility.

use super::*;
use crate::lint::{Level, LintId, LintMetadata, LintRegistryBuilder, LintStatus};
use crate::reachability::DeclarationsIteratorExtension;
use crate::types::ide_support::{ImportAliasResolution, definitions_for_name};

macro_rules! strict_lint {
    ($name:ident, $summary:literal) => {
        crate::declare_lint! {
            /// SOAC strict language rule, emitted only by explicit offline
            /// strict analysis with the shared project policy.
            pub(crate) static $name = {
                summary: $summary,
                status: LintStatus::stable("0.0.10"),
                default_level: Level::Error,
            }
        }
    };
}

strict_lint!(
    STRICT_FINAL_GLOBAL_REBIND,
    "detects rebinding a sealed final strict global"
);
strict_lint!(
    STRICT_FINAL_GLOBAL_DELETE,
    "detects deleting a sealed final strict global"
);
strict_lint!(
    STRICT_CLASS_MUTATION,
    "detects mutation of a participating sealed strict class"
);
strict_lint!(
    STRICT_FINAL_CLASS_SUBCLASS,
    "detects subclassing an enforced-final strict class"
);
strict_lint!(
    STRICT_FINAL_METHOD_OVERRIDE,
    "detects overriding an enforced-final strict method"
);
strict_lint!(
    STRICT_INSTANCE_METHOD_SHADOW,
    "detects writes shadowing a protected strict method"
);
strict_lint!(
    STRICT_CLASSVAR_INSTANCE_WRITE,
    "detects instance writes to a strict ClassVar"
);
strict_lint!(
    STRICT_INCOMPATIBLE_FIELD_WRITE,
    "detects incompatible writes under the checked-field policy"
);
strict_lint!(
    STRICT_INCOMPATIBLE_OVERRIDE,
    "detects incompatible participating strict method overrides"
);

pub(crate) fn register_lints(registry: &mut LintRegistryBuilder) {
    for lint in [
        &STRICT_FINAL_GLOBAL_REBIND,
        &STRICT_FINAL_GLOBAL_DELETE,
        &STRICT_CLASS_MUTATION,
        &STRICT_FINAL_CLASS_SUBCLASS,
        &STRICT_FINAL_METHOD_OVERRIDE,
        &STRICT_INSTANCE_METHOD_SHADOW,
        &STRICT_CLASSVAR_INSTANCE_WRITE,
        &STRICT_INCOMPATIBLE_FIELD_WRITE,
        &STRICT_INCOMPATIBLE_OVERRIDE,
    ] {
        registry.register_lint(lint);
    }
}

fn mutable_globals(db: &dyn Db, file: ProgramFile<'_>) -> BTreeSet<String> {
    struct GlobalDeclarations<'db> {
        db: &'db dyn Db,
        file: ProgramFile<'db>,
        names: BTreeSet<String>,
    }
    impl<'ast> Visitor<'ast> for GlobalDeclarations<'_> {
        fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
            if let ast::Stmt::Global(global) = statement {
                // In ordinary Python a module-level `global` has no effect,
                // so ty correctly does not mark its Symbol as global. SOAC's
                // language contract retains the declaration itself; use the
                // semantic index to verify its actual lexical target.
                let index = semantic_index(self.db, self.file);
                for name in &global.names {
                    let scope = index.expression_scope_id(name);
                    if let Some(symbol) = index.place_table(scope).symbol_id(name.as_str())
                        && index.symbol_resolves_to_global_scope(symbol, scope)
                    {
                        self.names.insert(name.to_string());
                    }
                }
            }
            visitor::walk_stmt(self, statement);
        }
    }
    let parsed = parsed_module(db, file.python_file(db)).load(db);
    let mut declarations = GlobalDeclarations {
        db,
        file,
        names: BTreeSet::new(),
    };
    declarations.visit_body(parsed.suite());
    declarations.names
}

fn is_strict(db: &dyn Db, file: ProgramFile<'_>) -> bool {
    if file.analysis_policy(db).dialect != AnalysisDialect::SoacStrictV1 {
        return false;
    }
    let parsed = parsed_module(db, file.python_file(db)).load(db);
    if !parsed.errors().is_empty() || !semantic_index(db, file).semantic_syntax_errors().is_empty()
    {
        return false;
    }
    parsed.suite().iter().any(|statement| matches!(statement,
        ast::Stmt::ImportFrom(import) if import.level == 0 && import.module.as_deref() == Some("__future__")
            && import.names.iter().any(|alias| alias.name.as_str() == "strict")))
}

pub(super) fn check(exporter: &mut Exporter<'_>, body: &[ast::Stmt]) {
    if exporter.module.source_dialect == facts::SourceDialect::SoacStrict {
        let mutable = mutable_globals(exporter.db, exporter.model.program_file());
        for name in mutable {
            if let Some(binding) = exporter
                .module
                .global_bindings
                .iter_mut()
                .find(|binding| binding.name == name)
            {
                binding.mutability = facts::GlobalMutability::ExplicitlyMutable;
            } else {
                exporter
                    .module
                    .global_bindings
                    .push(facts::GlobalBindingFact {
                        name,
                        mutability: facts::GlobalMutability::ExplicitlyMutable,
                        value_type: facts::StaticType::Unknown,
                        definition: None,
                        uncertainty: BTreeSet::from([facts::UncertaintyReason::Unknown]),
                    });
            }
        }
    }
    // Inheriting from a locally known dynamic class is not a construction
    // contract, even if its metaclass happens to be exactly `type`.
    loop {
        let dynamic: BTreeSet<_> = exporter
            .module
            .classes
            .iter()
            .filter(|class| {
                matches!(
                    class.participation,
                    facts::ParticipationProposal::Dynamic(_)
                )
            })
            .map(|class| class.identity.clone())
            .collect();
        let mut changed = false;
        for class in &mut exporter.module.classes {
            if class.participation == facts::ParticipationProposal::Candidate
                && class
                    .inheritance
                    .linearized_bases
                    .iter()
                    .any(|base| dynamic.contains(&base.definition))
            {
                class.participation = facts::ParticipationProposal::Dynamic(BTreeSet::from([
                    facts::DynamicClassReason::MutableBase,
                ]));
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    StrictChecker {
        exporter,
        deferred_depth: 0,
    }
    .visit_body(body);
}

struct StrictChecker<'a, 'db> {
    exporter: &'a mut Exporter<'db>,
    /// A general function can run after module sealing. Module/class-body
    /// initialization is deliberately not mislabeled as a sealed execution.
    deferred_depth: usize,
}

impl<'db> StrictChecker<'_, 'db> {
    fn report(
        &mut self,
        code: facts::DiagnosticCode,
        lint: &'static LintMetadata,
        range: TextRange,
        related: Vec<facts::SourceIdentity>,
        message: String,
    ) {
        let db = self.exporter.db;
        let file = self.exporter.model.program_file();
        let selection = db.rule_selection(file.file(db)).get(LintId::of(lint));
        let suppressions = crate::suppression::suppressions(db, file.python_file(db));
        let suppression = suppressions.find_suppression(range, LintId::of(lint));
        if selection.is_some()
            && let Some(suppression) = suppression
        {
            self.exporter.used_suppressions.push(suppression.id());
        }
        let ignored = suppression.is_some()
            || !matches!(selection, Some((Severity::Error | Severity::Fatal, _)));
        let range = source_range(range);
        self.exporter
            .module
            .diagnostics
            .push(facts::StrictDiagnostic {
                code,
                severity: if ignored {
                    facts::DiagnosticSeverity::Warning
                } else {
                    facts::DiagnosticSeverity::Error
                },
                source_range: range,
                scope: facts::DiagnosticScope::Site(range),
                related_definitions: related,
                suppressed: ignored,
                message,
            });
    }

    fn builtin(&self, ty: Type<'db>, name: &str) -> bool {
        let function = match ty {
            Type::FunctionLiteral(function) => Some(function),
            Type::BoundMethod(method) => Some(method.function(self.exporter.db)),
            _ => None,
        };
        function
            .and_then(|function| {
                self.exporter
                    .definition(function.definition(self.exporter.db))
            })
            .is_some_and(|definition| {
                definition.module.module_name == "builtins" && definition.lexical_qualname == name
            })
    }

    fn literal_name(&self, expression: &ast::Expr, model: &SemanticModel<'db>) -> Option<String> {
        expression
            .inferred_type(model)?
            .as_string_literal()
            .map(|literal| literal.value(self.exporter.db).to_owned())
    }

    /// Resolve known namespace aliases through unique checker definitions. A
    /// union of reachable definitions is not arbitrarily reduced to the first.
    fn namespace(
        &self,
        expression: &ast::Expr,
        model: &SemanticModel<'db>,
        depth: usize,
    ) -> Option<ProgramFile<'db>> {
        if depth > 12 {
            return None;
        }
        let db = self.exporter.db;
        match expression {
            ast::Expr::Call(call) => {
                let callable = call.func.inferred_type(model)?;
                if self.builtin(callable, "globals") && call.arguments.is_empty() {
                    return Some(model.program_file());
                }
                if self.builtin(callable, "vars") && call.arguments.keywords.is_empty() {
                    match call.arguments.args.as_ref() {
                        [argument] => {
                            return self.module_value(argument.inferred_type(model)?, model);
                        }
                        [] if model
                            .scope(expression.into())
                            .is_some_and(|scope| scope.is_global()) =>
                        {
                            return Some(model.program_file());
                        }
                        _ => {}
                    }
                }
            }
            ast::Expr::Attribute(attribute) if attribute.attr.as_str() == "__dict__" => {
                return self.module_value(attribute.value.inferred_type(model)?, model);
            }
            ast::Expr::Attribute(attribute) if attribute.attr.as_str() == "__globals__" => {
                let function = attribute
                    .value
                    .inferred_type(model)?
                    .as_function_literal()?;
                return Some(function.definition(db).program_file(db));
            }
            ast::Expr::Name(name) => {
                let definitions = definitions_for_name(
                    model,
                    name.id.as_str(),
                    name.into(),
                    ImportAliasResolution::ResolveAliases,
                );
                let mut definitions: Vec<_> = definitions
                    .into_iter()
                    .filter_map(|definition| definition.definition())
                    .collect();
                definitions.sort();
                definitions.dedup();
                let [definition] = definitions.as_slice() else {
                    return None;
                };
                let file = definition.program_file(db);
                // A declared mutable global alias can have an unrelated value
                // by the time a general function is invoked.
                if definition.scope(db).file_scope_id(db).is_global()
                    && mutable_globals(db, file).contains(name.id.as_str())
                {
                    return None;
                }
                let parsed = parsed_module(db, file.python_file(db)).load(db);
                let value = match definition.kind(db) {
                    DefinitionKind::Assignment(assignment) => Some(assignment.value(&parsed)),
                    DefinitionKind::AnnotatedAssignment(assignment) => assignment.value(&parsed),
                    _ => None,
                }?;
                return self.namespace(value, &SemanticModel::new(db, file), depth + 1);
            }
            _ => {}
        }
        None
    }

    fn module_value(&self, ty: Type<'db>, model: &SemanticModel<'db>) -> Option<ProgramFile<'db>> {
        let Type::ModuleLiteral(module) = ty else {
            return None;
        };
        let file = module.module(self.exporter.db).file(self.exporter.db)?;
        Some(model.program().program_file(self.exporter.db, file))
    }

    fn global_write(&mut self, file: ProgramFile<'db>, name: &str, delete: bool, range: TextRange) {
        let db = self.exporter.db;
        // No source-only proof of sealing is available for a circular import
        // during module-body execution. General functions must be valid after
        // sealing regardless of whether a particular call happens during init.
        if self.deferred_depth == 0
            || !is_strict(db, file)
            || mutable_globals(db, file).contains(name)
        {
            return;
        }
        let binding = all_end_of_scope_members(db, ty_python_core::global_scope(db, file))
            .find(|member| member.member.name.as_str() == name);
        let Some(binding) = binding else {
            return;
        }; // previously absent: append-once is legal
        let related = self
            .exporter
            .definition(binding.first_reachable_definition)
            .into_iter()
            .collect();
        self.report(
            if delete { facts::DiagnosticCode::StrictFinalGlobalDelete } else { facts::DiagnosticCode::StrictFinalGlobalRebind },
            if delete { &STRICT_FINAL_GLOBAL_DELETE } else { &STRICT_FINAL_GLOBAL_REBIND },
            range, related,
            format!("Strict global `{name}` is final after module sealing; declare it with a lexical `global` statement to permit mutation"),
        );
    }

    fn participating(&self, class: ClassLiteral<'db>) -> Option<facts::ClassTypeFact> {
        let reference = self.exporter.class_reference(class)?;
        self.exporter
            .module
            .classes
            .iter()
            .find(|class| {
                class.identity == reference.definition
                    && class.participation == facts::ParticipationProposal::Candidate
            })
            .cloned()
    }

    fn inherited_method(
        &self,
        owner: &facts::ClassTypeFact,
        name: &str,
    ) -> Option<facts::MethodTypeFact> {
        std::iter::once(&owner.identity)
            .chain(
                owner
                    .inheritance
                    .linearized_bases
                    .iter()
                    .map(|base| &base.definition),
            )
            .find_map(|identity| {
                self.exporter
                    .module
                    .classes
                    .iter()
                    .find(|class| &class.identity == identity)
                    .and_then(|class| class.methods.iter().find(|method| method.name == name))
                    .cloned()
            })
    }

    fn attribute_write(
        &mut self,
        receiver: Type<'db>,
        name: &str,
        value: Option<Type<'db>>,
        delete: bool,
        range: TextRange,
    ) {
        let db = self.exporter.db;
        let receiver = match receiver {
            Type::TypeVar(variable) if variable.typevar(db).is_self(db) => variable
                .typevar(db)
                .upper_bound(db, &self.exporter.env)
                .unwrap_or(receiver),
            _ => receiver,
        };
        if let Some(file) = self.module_value(receiver, &self.exporter.model) {
            self.global_write(file, name, delete, range);
            return;
        }
        if let Type::ClassLiteral(class) = receiver {
            if self.deferred_depth > 0
                && let Some(owner) = self.participating(class)
            {
                self.report(
                    facts::DiagnosticCode::StrictClassMutation,
                    &STRICT_CLASS_MUTATION,
                    range,
                    vec![owner.identity],
                    format!(
                        "Participating strict class member `{name}` cannot be mutated after sealing"
                    ),
                );
            }
            return;
        }
        let Type::NominalInstance(instance) = receiver else {
            return;
        };
        let Some(owner) = self.participating(instance.class_literal(db, &self.exporter.env)) else {
            return;
        };
        let member = receiver.class_member(db, &self.exporter.env, name);
        if member.qualifiers.contains(TypeQualifiers::CLASS_VAR) {
            self.report(
                facts::DiagnosticCode::StrictClassvarInstanceWrite,
                &STRICT_CLASSVAR_INSTANCE_WRITE,
                range,
                vec![owner.identity],
                format!("Strict ClassVar `{name}` is a class variable, not an instance field"),
            );
            return;
        }
        let field = receiver.instance_member(db, &self.exporter.env, name);
        // A declared instance field intentionally takes precedence over an
        // inherited non-data method. Inferred stores alone cannot authorize
        // shadowing: they are the mutation this rule is supposed to diagnose.
        let declared_field = instance
            .class_literal(db, &self.exporter.env)
            .as_static()
            .is_some_and(|class| {
                class
                    .iter_mro(db, None)
                    .filter_map(ClassBase::into_class)
                    .filter_map(|base| base.class_literal(db).as_static())
                    .any(|base| {
                        base.own_annotated_qualifiers(db).iter().any(
                            |(field_name, qualifiers, _)| {
                                field_name.as_str() == name
                                    && !qualifiers.contains(TypeQualifiers::CLASS_VAR)
                            },
                        ) || crate::attribute_declarations(db, base.body_scope(db), name).any(
                            |(declarations, _)| {
                                declarations.any_reachable(db, |declaration| {
                                    declaration.is_defined_and(|definition| {
                                        crate::types::inferred_declaration(db, definition)
                                            .declared()
                                            .is_some()
                                    })
                                })
                            },
                        )
                    })
            });
        if !declared_field
            && let Some(method) = self.inherited_method(&owner, name)
            && matches!(
                method.binding,
                facts::MethodBinding::Instance
                    | facts::MethodBinding::Class
                    | facts::MethodBinding::Static
            )
        {
            self.report(
                facts::DiagnosticCode::StrictInstanceMethodShadow,
                &STRICT_INSTANCE_METHOD_SHADOW,
                range,
                method.implementation.into_iter().collect(),
                format!("Instance mutation of `{name}` would shadow a protected strict method"),
            );
            return;
        }
        if !delete
            && self.exporter.module.language_policy.checked_fields
                == facts::CheckedFieldPolicy::SupportedAnnotations
            && let Some(value) = value
            && let Some(field_type) = field.place.ignore_possibly_undefined()
            && self
                .exporter
                .value_type(field_type)
                .has_supported_boundary_shape()
            && !self.exporter.value_type(value).contains_uncertainty()
            && !value.is_assignable_to(db, &self.exporter.env, field_type)
        {
            self.report(facts::DiagnosticCode::StrictIncompatibleFieldWrite, &STRICT_INCOMPATIBLE_FIELD_WRITE, range,
                vec![owner.identity], format!("Value written to `{name}` is incompatible with the enabled strict checked-field policy"));
        }
    }

    fn target(&mut self, target: &ast::Expr, value: Option<&ast::Expr>, delete: bool) {
        match target {
            ast::Expr::Attribute(attribute) => {
                let receiver = attribute
                    .value
                    .inferred_type(&self.exporter.model)
                    .unwrap_or_else(Type::unknown);
                let value = value.and_then(|value| value.inferred_type(&self.exporter.model));
                self.attribute_write(
                    receiver,
                    attribute.attr.as_str(),
                    value,
                    delete,
                    target.range(),
                );
            }
            ast::Expr::Subscript(subscript) => {
                if let Some(file) = self.namespace(&subscript.value, &self.exporter.model, 0)
                    && let Some(name) = self.literal_name(&subscript.slice, &self.exporter.model)
                {
                    self.global_write(file, &name, delete, target.range());
                }
            }
            ast::Expr::Tuple(tuple) => {
                for item in &tuple.elts {
                    self.target(item, None, delete);
                }
            }
            ast::Expr::List(list) => {
                for item in &list.elts {
                    self.target(item, None, delete);
                }
            }
            ast::Expr::Starred(starred) => self.target(&starred.value, None, delete),
            _ => {}
        }
    }

    fn call(&mut self, call: &ast::ExprCall) {
        let callable = call
            .func
            .inferred_type(&self.exporter.model)
            .unwrap_or_else(Type::unknown);
        let is_set =
            self.builtin(callable, "setattr") || self.builtin(callable, "object.__setattr__");
        let is_del =
            self.builtin(callable, "delattr") || self.builtin(callable, "object.__delattr__");
        if (is_set || is_del) && call.arguments.keywords.is_empty() {
            if let [receiver, name, rest @ ..] = call.arguments.args.as_ref()
                && ((is_set && rest.len() == 1) || (is_del && rest.is_empty()))
                && let Some(name) = self.literal_name(name, &self.exporter.model)
            {
                let receiver = receiver
                    .inferred_type(&self.exporter.model)
                    .unwrap_or_else(Type::unknown);
                let value = rest
                    .first()
                    .and_then(|value| value.inferred_type(&self.exporter.model));
                self.attribute_write(receiver, &name, value, is_del, call.range());
            }
            return;
        }
        let ast::Expr::Attribute(attribute) = &*call.func else {
            return;
        };
        let Some(file) = self.namespace(&attribute.value, &self.exporter.model, 0) else {
            return;
        };
        match attribute.attr.as_str() {
            "__setitem__" | "__delitem__" | "pop" => {
                if let Some(key) = call.arguments.args.first()
                    && let Some(name) = self.literal_name(key, &self.exporter.model)
                {
                    self.global_write(
                        file,
                        &name,
                        attribute.attr.as_str() != "__setitem__",
                        call.range(),
                    );
                }
            }
            "update" => {
                if let Some(ast::Expr::Dict(dictionary)) = call.arguments.args.first() {
                    for item in &dictionary.items {
                        if let Some(key) = &item.key
                            && let Some(name) = self.literal_name(key, &self.exporter.model)
                        {
                            self.global_write(file, &name, false, key.range());
                        }
                    }
                }
                for keyword in &call.arguments.keywords {
                    if let Some(name) = &keyword.arg {
                        self.global_write(file, name.as_str(), false, keyword.range());
                    }
                }
            }
            "clear" => {
                // Any known existing final key makes clearing the whole module
                // dictionary prohibited; one diagnostic is sufficient.
                let mut names: Vec<_> = all_end_of_scope_members(
                    self.exporter.db,
                    ty_python_core::global_scope(self.exporter.db, file),
                )
                .map(|member| member.member.name.to_string())
                .collect();
                names.sort();
                names.dedup();
                let mutable = mutable_globals(self.exporter.db, file);
                if let Some(name) = names.iter().find(|name| !mutable.contains(*name)) {
                    self.global_write(file, name, true, call.range());
                }
            }
            _ => {}
        }
    }

    fn class_definition(&mut self, node: &ast::StmtClassDef) {
        let db = self.exporter.db;
        let Some(class) = original_class_type(db, node.definition(&self.exporter.model))
            .and_then(ClassLiteral::as_static)
        else {
            return;
        };
        let owner = self.participating(class.into());
        let enforce_final = self.exporter.module.language_policy.typing_final_policy
            == facts::TypingFinalPolicy::EnforceForParticipatingClasses;
        for base in class.explicit_bases(db) {
            let Some(base) = base.to_class_type(db) else {
                continue;
            };
            if enforce_final
                && base.is_final(db)
                && let Some(base_owner) = self.participating(base.class_literal(db))
            {
                self.report(
                    facts::DiagnosticCode::StrictFinalClassSubclass,
                    &STRICT_FINAL_CLASS_SUBCLASS,
                    node.name.range(),
                    vec![base_owner.identity],
                    "Cannot subclass a participating strict class with enforced finality".into(),
                );
            }
        }
        let child_instance =
            Type::instance(db, &self.exporter.env, class.default_specialization(db));
        let mut seen_members = BTreeSet::new();
        for member in all_end_of_scope_members(db, class.body_scope(db)) {
            let name = member.member.name.as_str();
            if !seen_members.insert(name.to_owned()) {
                continue;
            }
            let inherited = class
                .iter_mro(db, None)
                .skip(1)
                .filter_map(ClassBase::into_class)
                .find_map(|base| {
                    let owner = self.participating(base.class_literal(db))?;
                    let method = owner
                        .methods
                        .iter()
                        .find(|method| method.name == name)?
                        .clone();
                    Some((base, method))
                });
            let Some((base, method)) = inherited else {
                continue;
            };
            let parsed =
                parsed_module(db, member.first_reachable_definition.python_file(db)).load(db);
            let range = member
                .first_reachable_definition
                .kind(db)
                .target_range(&parsed);
            if enforce_final && method.declared_final {
                self.report(
                    facts::DiagnosticCode::StrictFinalMethodOverride,
                    &STRICT_FINAL_METHOD_OVERRIDE,
                    range,
                    method.implementation.clone().into_iter().collect(),
                    format!("Cannot override enforced-final strict method `{name}`"),
                );
            }
            // Constructor signatures normally differ across subclasses, and a
            // declared instance field may replace an inherited non-data method.
            if matches!(name, "__init__" | "__new__" | "__init_subclass__") {
                continue;
            }
            let Some(own_method) = owner
                .as_ref()
                .and_then(|owner| owner.methods.iter().find(|method| method.name == name))
            else {
                continue;
            };
            let base_instance = Type::instance(db, &self.exporter.env, base);
            let child_ty = child_instance
                .member(db, &self.exporter.env, name)
                .place
                .ignore_possibly_undefined();
            let base_ty = base_instance
                .member(db, &self.exporter.env, name)
                .place
                .ignore_possibly_undefined();
            if let (Some(child_ty), Some(base_ty)) = (child_ty, base_ty)
                && (own_method.binding != method.binding
                    || !crate::types::overrides::is_assignable_method_override(
                        db,
                        &self.exporter.env,
                        child_ty,
                        base_ty,
                    ))
                && !self.exporter.value_type(child_ty).contains_uncertainty()
                && !self.exporter.value_type(base_ty).contains_uncertainty()
            {
                self.report(facts::DiagnosticCode::StrictIncompatibleOverride, &STRICT_INCOMPATIBLE_OVERRIDE, range,
                    method.implementation.into_iter().collect(), format!("Strict override `{name}` does not preserve its inherited binding and callable contract"));
            }
        }
    }
}

impl<'ast> Visitor<'ast> for StrictChecker<'_, '_> {
    fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
        match statement {
            ast::Stmt::Assign(assign) => {
                for target in &assign.targets {
                    self.target(target, Some(&assign.value), false);
                }
            }
            ast::Stmt::AnnAssign(assign) => {
                if let Some(value) = &assign.value {
                    self.target(&assign.target, Some(value), false);
                }
            }
            ast::Stmt::AugAssign(assign) => self.target(&assign.target, None, false),
            ast::Stmt::Delete(delete) => {
                for target in &delete.targets {
                    self.target(target, None, true);
                }
            }
            ast::Stmt::ClassDef(class) => self.class_definition(class),
            ast::Stmt::FunctionDef(function) => {
                for decorator in &function.decorator_list {
                    self.visit_decorator(decorator);
                }
                for parameter in function.parameters.iter_non_variadic_params() {
                    if let Some(default) = &parameter.default {
                        self.visit_expr(default);
                    }
                }
                self.deferred_depth += 1;
                self.visit_body(&function.body);
                self.deferred_depth -= 1;
                return;
            }
            _ => {}
        }
        visitor::walk_stmt(self, statement);
    }

    fn visit_annotation(&mut self, _annotation: &'ast ast::Expr) {}

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        match expression {
            ast::Expr::Call(call) => self.call(call),
            ast::Expr::Lambda(lambda) => {
                if let Some(parameters) = &lambda.parameters {
                    for parameter in parameters.iter_non_variadic_params() {
                        if let Some(default) = &parameter.default {
                            self.visit_expr(default);
                        }
                    }
                }
                self.deferred_depth += 1;
                self.visit_expr(&lambda.body);
                self.deferred_depth -= 1;
                return;
            }
            _ => {}
        }
        visitor::walk_expr(self, expression);
    }
}
