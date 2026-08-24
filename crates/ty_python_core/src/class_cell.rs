use ruff_index::IndexSlice;

use crate::scope::{FileScopeId, NodeWithScopeKind, Scope, ScopeKind};

/// The implicit closure cell supplied by one lexical class construction.
///
/// This is distinct from a class namespace attribute named `__class__`. Methods and their nested
/// functions can share and mutate this cell without creating a class or module dictionary binding.
#[derive(
    Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, get_size2::GetSize, salsa::SalsaValue,
)]
pub struct ImplicitClassCell {
    class_scope: FileScopeId,
}

impl ImplicitClassCell {
    pub fn class_scope(self) -> FileScopeId {
        self.class_scope
    }

    /// The callable boundary at which this cell enters lexical closure lookup. Eager class-body
    /// expressions and unrelated functions installed as class attributes are not such boundaries.
    pub(crate) fn for_callable_scope(
        scopes: &IndexSlice<FileScopeId, Scope>,
        callable_scope: FileScopeId,
    ) -> Option<Self> {
        let callable = &scopes[callable_scope];
        let parent = callable.parent()?;
        let class_scope = match callable.node() {
            NodeWithScopeKind::Function(_) => {
                if scopes[parent].kind() == ScopeKind::TypeParams {
                    scopes[parent].parent()?
                } else {
                    parent
                }
            }
            NodeWithScopeKind::Lambda(_) | NodeWithScopeKind::GeneratorExpression(_) => parent,
            _ => return None,
        };
        scopes[class_scope]
            .kind()
            .is_class()
            .then_some(Self { class_scope })
    }

    /// Resolve a free or nonlocal `__class__` reference using completed lexical scope information.
    /// The callback reports explicit local/global owners; nonlocal declarations only forward.
    /// Class namespace bindings are visible in the starting class scope, never through a closure.
    pub(crate) fn resolve(
        scopes: &IndexSlice<FileScopeId, Scope>,
        start: FileScopeId,
        mut has_explicit_owner: impl FnMut(FileScopeId) -> bool,
    ) -> Option<Self> {
        let mut next = Some(start);
        while let Some(scope_id) = next {
            let scope = &scopes[scope_id];
            if scope.kind().is_module() {
                return None;
            }
            if (scope_id == start || scope.kind().is_function_like())
                && has_explicit_owner(scope_id)
            {
                return None;
            }
            if let Some(cell) = Self::for_callable_scope(scopes, scope_id) {
                // A generic method's type parameter scope may explicitly own the same name.
                // Check that intervening lexical scope before reaching the class cell.
                let mut parent = scope.parent();
                while let Some(parent_id) = parent {
                    if parent_id == cell.class_scope {
                        break;
                    }
                    if has_explicit_owner(parent_id) {
                        return None;
                    }
                    parent = scopes[parent_id].parent();
                }
                return Some(cell);
            }
            next = scope.parent();
        }
        None
    }
}
