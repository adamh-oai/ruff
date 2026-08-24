//! Explicit language policy for offline SOAC analysis.
//!
//! A dialect is analysis input, not a conclusion drawn from a future import or
//! an annotation. Selecting it does not authenticate a runtime contract.

use ruff_python_ast::PythonVersion;

/// The language dialect selected by the embedding application.
///
/// A database must keep this policy immutable, or expose changes through tracked
/// Salsa inputs. Ordinary Python remains the default for all existing consumers.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, get_size2::GetSize)]
pub enum AnalysisDialect {
    #[default]
    Python,
    /// Version 1 of SOAC's explicit strict-analysis dialect.
    ///
    /// Allows the strict future and requires conservative equality and generic
    /// narrowing. It does not make annotations into runtime-enforced facts.
    SoacStrictV1,
}

/// The effective dialect and Python version for one interpretation of a file.
///
/// Exporters must include both in their authenticated artifact and validate the
/// target against the runtime. Script metadata can select a different version
/// from the surrounding project; the dialect must not silently override it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, get_size2::GetSize)]
pub struct AnalysisPolicy {
    pub dialect: AnalysisDialect,
    pub python_version: PythonVersion,
}
