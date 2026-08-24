//! Source-token validity for exact literal inference in SOAC analysis.

use ruff_db::parsed::parsed_module;
use ruff_db::source::source_text;
use ty_python_core::{AnalysisDialect, ProgramFile};

use crate::Db;

/// Check the actual file being inferred, including ordinary dependencies and
/// vendored stubs. Cache by the existing source/version/dialect key; a later
/// source edit must not reuse an earlier lossless decision.
#[salsa::tracked]
pub(crate) fn source_literals_supported(db: &dyn Db, file: ProgramFile<'_>) -> bool {
    if file.analysis_policy(db).dialect != AnalysisDialect::SoacStrictV1 {
        return true;
    }
    let source = source_text(db, file.file(db));
    let parsed = parsed_module(db, file.python_file(db)).load(db);
    source.read_error().is_none()
        && parsed.has_valid_syntax()
        && soac_source::validate_source_literals(source.as_str(), parsed.tokens()).is_ok()
}
