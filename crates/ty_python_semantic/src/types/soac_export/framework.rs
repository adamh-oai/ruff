//! Automatic framework fallback at the explicit SOAC-consumer boundary.
//!
//! Ordinary ty checking and its cached diagnostics remain unchanged. Only an
//! unresolved-attribute diagnostic at an actual attribute expression can be a
//! warning here, and only when that expression's real semantic receiver is an
//! already dynamic framework class or a user-defined metaclass. Lexical
//! containment, an ignore, Any, and an arbitrary mutable base are insufficient.

use ruff_db::diagnostic::{Diagnostic, UnifiedFile};

use super::*;
use crate::types::diagnostic::UNRESOLVED_ATTRIBUTE;

impl<'db> Exporter<'db> {
    pub(super) fn framework_attribute_fallback(
        &mut self,
        diagnostic: &Diagnostic,
    ) -> Option<facts::SourceIdentity> {
        if self.module.source_dialect != facts::SourceDialect::SoacStrict
            || diagnostic.id().as_lint() != Some(UNRESOLVED_ATTRIBUTE.name())
        {
            return None;
        }
        let span = diagnostic.primary_span()?;
        if span.file() != &UnifiedFile::Ty(self.model.program_file().file(self.db)) {
            return None;
        }
        let range = source_range(span.range()?);
        let receiver = *self.attribute_receivers.get(&range)?;
        let (class, mut uncertainty) = self.framework_receiver(receiver)?;
        uncertainty.insert(facts::UncertaintyReason::Unknown);

        // A containing attribute/call consumes this unresolved value, including
        // when it is an argument rather than the callee. Remove those optional
        // proposals instead of treating a warning as positive type evidence.
        // Unrelated source signatures keep their independent checked contracts.
        for site in &mut self.module.attribute_sites {
            if contains(site.identity.expression_range, range) {
                site.receiver_type = facts::StaticType::Unknown;
                if site.value_type.is_some() {
                    site.value_type = Some(facts::StaticType::Unknown);
                }
                site.uncertainty.extend(uncertainty.iter().copied());
            }
        }
        for call in &mut self.module.call_sites {
            if contains(call.identity.expression_range, range) {
                if let Some(receiver) = &mut call.receiver {
                    receiver.value_type = facts::StaticType::Unknown;
                    receiver.uncertainty.extend(uncertainty.iter().copied());
                }
                call.candidate_targets = vec![facts::CallableTargetFact::Dynamic];
                call.binding = facts::CallBindingFact::Dynamic;
                call.signature = unknown_signature();
                call.result_type = facts::StaticType::Unknown;
                call.uncertainty = facts::CallUncertainty::Dynamic;
            }
        }
        Some(class.definition)
    }

    fn framework_receiver(
        &self,
        receiver: Type<'db>,
    ) -> Option<(facts::ClassReference, BTreeSet<facts::UncertaintyReason>)> {
        let db = self.db;
        let class = receiver
            .to_class_type(db)
            .or_else(|| receiver.nominal_class(db, &self.env))?
            .class_literal(db)
            .as_static()?;
        let reference = self.class_reference(class.into())?;
        if class.try_mro(db, None).is_err() {
            return None;
        }
        let mut uncertainty = BTreeSet::new();
        // In `Meta.__new__`, ty models the result of `type.__new__` as
        // synthetic Self bounded by the actual Meta. This is a class object,
        // not a fixed-layout candidate instance. Recognize its semantic MRO;
        // neither the method spelling nor a name such as "Meta" is authority.
        if class.known(db) != Some(KnownClass::Type)
            && class.iter_mro(db, None).any(|base| {
                matches!(base, ClassBase::Class(base) if base.known(db) == Some(KnownClass::Type))
            })
        {
            uncertainty.insert(facts::UncertaintyReason::DynamicMetaclass);
        }
        // The flattened semantic MRO propagates a genuine framework exclusion
        // through locally known bases without treating all MutableBase reasons
        // (for example a list subclass) as an unresolved-attribute exemption.
        for base in class.iter_mro(db, None) {
            let ClassBase::Class(base) = base else {
                continue;
            };
            let Some(base) = self.class_reference(base.class_literal(db)) else {
                continue;
            };
            let Some(proposal) = self
                .module
                .classes
                .iter()
                .find(|proposal| proposal.identity == base.definition)
            else {
                continue;
            };
            let facts::ParticipationProposal::Dynamic(reasons) = &proposal.participation else {
                continue;
            };
            for reason in reasons {
                match reason {
                    facts::DynamicClassReason::NonParticipatingMetaclass => {
                        uncertainty.insert(facts::UncertaintyReason::DynamicMetaclass);
                    }
                    facts::DynamicClassReason::UnknownDecorator => {
                        uncertainty.insert(facts::UncertaintyReason::DynamicDecorator);
                    }
                    facts::DynamicClassReason::FrameworkManaged => {
                        uncertainty.insert(facts::UncertaintyReason::UnsupportedType);
                    }
                    facts::DynamicClassReason::CustomAttributeHooks => {
                        uncertainty.insert(facts::UncertaintyReason::DynamicDescriptor);
                    }
                    _ => {}
                }
            }
        }
        (!uncertainty.is_empty()).then_some((reference, uncertainty))
    }
}

fn contains(outer: facts::SourceRange, inner: facts::SourceRange) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}
