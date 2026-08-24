use std::fmt::Formatter;
use std::panic::RefUnwindSafe;
use std::sync::Arc;
use std::{cmp, fmt};

pub use self::changes::ChangeResult;
use crate::CollectReporter;
use crate::metadata::settings::file_settings;
use crate::script::Script;
use crate::{ProgressReporter, Project, ProjectMetadata};
use get_size2::StandardTracker;
use ruff_db::Db as SourceDb;
use ruff_db::diagnostic::Diagnostic;
use ruff_db::files::{File, Files};
use ruff_db::system::System;
use ruff_db::vendored::VendoredFileSystem;
use salsa::{Database, Event, Setter};
use ty_python_core::program::{FallibleStrategy, MisconfigurationStrategy, UseDefaultStrategy};
use ty_python_core::{AnalysisDialect, ProgramFile};
use ty_python_semantic::lint::{LintRegistry, RuleSelection};
use ty_python_semantic::{AnalysisSettings, Db as SemanticDb, PythonVersionWithSource};

mod changes;

#[salsa::db]
pub trait Db: SemanticDb {
    fn project(&self) -> Project;

    fn dyn_clone(&self) -> Box<dyn Db>;
}

/// Tracked so that a change to the open-file set only invalidates queries
/// for files whose open state actually changed.
#[salsa::tracked(heap_size=ruff_memory_usage::heap_size, returns(copy))]
fn is_open_file_impl(db: &dyn Db, file: File) -> bool {
    db.project().open_files(db).contains(&file)
}

#[salsa::db]
#[derive(Clone)]
pub struct ProjectDatabase {
    // This handle must remain stable for the lifetime of the database.
    //
    // Many tracked queries branch on the untracked `db.project()` read before
    // consulting tracked `Project` fields. Replacing the handle during reload
    // therefore changes query behavior outside salsa's dependency graph and can
    // trigger stale results.
    //
    // Structural reloads must update the existing `Project` in place via salsa
    // setters instead of swapping in a freshly constructed handle.
    project: Option<Project>,
    files: Files,

    // Immutable for the lifetime of this database and all its snapshots. Choosing
    // another dialect requires a new database, including its vendored file set.
    analysis_dialect: AnalysisDialect,

    // IMPORTANT: Never return clones of `system` outside `ProjectDatabase` (only return references)
    // or the "trick" to get a mutable `Arc` in `Self::system_mut` is no longer guaranteed to work.
    system: Arc<dyn System + Send + Sync + RefUnwindSafe>,

    // IMPORTANT: This field must be the last because we use `trigger_cancellation` (drops all other storage references)
    // to drop all other references to the database, which gives us exclusive access to other `Arc`s stored on this db.
    // However, for this to work it's important that the `storage` is dropped AFTER any `Arc` that
    // we try to mutably borrow using `Arc::get_mut` (like `system`).
    storage: salsa::Storage<ProjectDatabase>,
}

impl ProjectDatabase {
    /// Creates a new database, returning an error if the project metadata is misconfigured.
    pub fn fallible<S>(project_metadata: ProjectMetadata, system: S) -> anyhow::Result<Self>
    where
        S: System + 'static + Send + Sync + RefUnwindSafe,
    {
        Self::fallible_with_analysis_dialect(project_metadata, system, AnalysisDialect::Python)
    }

    /// Creates a database with an explicitly selected, immutable analysis dialect.
    ///
    /// SOAC mode selects its matched future stub and forces conservative analysis
    /// after per-file overrides. It does not alter source bytes, authenticate
    /// contracts, or change the configured target Python version. Exporters must
    /// validate each `ProgramFile::analysis_policy` against their target runtime.
    pub fn fallible_with_analysis_dialect<S>(
        project_metadata: ProjectMetadata,
        system: S,
        analysis_dialect: AnalysisDialect,
    ) -> anyhow::Result<Self>
    where
        S: System + 'static + Send + Sync + RefUnwindSafe,
    {
        Self::new(
            project_metadata,
            system,
            analysis_dialect,
            &FallibleStrategy,
        )
    }

    /// Creates a new database, substituting default values for any misconfigured settings.
    pub fn use_defaults<S>(project_metadata: ProjectMetadata, system: S) -> Self
    where
        S: System + 'static + Send + Sync + RefUnwindSafe,
    {
        let Ok(db) = Self::new(
            project_metadata,
            system,
            AnalysisDialect::Python,
            &UseDefaultStrategy,
        );
        db
    }

    /// Permanently freezes the most heavily read inputs that are immutable during a one-shot check.
    ///
    /// This is intentionally not exhaustive. It includes the program, the most heavily
    /// read immutable [`Project`] inputs, and every field on files created after this call. Existing
    /// files retain their durability. This must not be used by incremental consumers or checks that
    /// apply fixes.
    pub fn freeze(&mut self) {
        self.project().freeze(self);
        self.files.freeze();
    }

    /// Permanently marks the project as never having open files.
    pub fn freeze_open_files(&mut self) {
        let project = self.project();
        project.freeze_open_files(self);
    }

    fn new<S, Strategy: MisconfigurationStrategy>(
        project_metadata: ProjectMetadata,
        system: S,
        analysis_dialect: AnalysisDialect,
        strategy: &Strategy,
    ) -> Result<Self, Strategy::Error<anyhow::Error>>
    where
        S: System + 'static + Send + Sync + RefUnwindSafe,
    {
        let mut db = Self {
            project: None,
            analysis_dialect,
            storage: salsa::Storage::new(if tracing::enabled!(tracing::Level::TRACE) {
                Some(Box::new({
                    move |event: Event| {
                        if matches!(event.kind, salsa::EventKind::WillCheckCancellation) {
                            return;
                        }

                        tracing::trace!("Salsa event: {event:?}");
                    }
                }))
            } else {
                None
            }),
            files: Files::default(),
            system: Arc::new(system),
        };

        // TODO: Use the `program_settings` to compute the key for the database's persistent
        //   cache and load the cache if it exists.
        //   we may want to have a dedicated method for this?
        // Important: For persistent caching it's essential that we can compute the
        // cache key before loading the DB. Because of that, access to the `db` (other than system and vendored) is
        // strictly forbidden before resolving the `program_settings`.

        let merged_options = project_metadata.to_merged_options();

        let (program_settings, program_settings_diagnostics) = strategy
            .to_anyhow(merged_options.to_program_settings(db.system(), db.vendored(), strategy))?;

        // This must be called before `from_metadata`, or the `SearchPath` root
        // will take precedence over the `Project` root, resulting in
        // all project files having HIGH durability.
        project_metadata.try_add_project_root(&db);

        let (settings, mut settings_diagnostics) = strategy
            .map_err(merged_options.to_settings(&db, strategy), |error| {
                anyhow::anyhow!("{}", error.pretty(&db))
            })?;
        settings_diagnostics.extend(
            program_settings_diagnostics
                .into_iter()
                .map(|diagnostic| diagnostic.into_diagnostic(&db)),
        );

        db.project = Some(Project::from_metadata(
            &db,
            project_metadata,
            settings,
            program_settings,
            settings_diagnostics,
        ));

        Ok(db)
    }

    /// Checks the files in the project and its dependencies as per the project's check mode.
    ///
    /// Use [`set_check_mode`] to update the check mode.
    ///
    /// [`set_check_mode`]: ProjectDatabase::set_check_mode
    pub fn check(&self) -> Vec<Diagnostic> {
        let mut collector = CollectReporter::default();
        self.project().check(self, &mut collector);
        collector.into_sorted(self)
    }

    /// Checks the files in the project and its dependencies, using the given reporter.
    ///
    /// Use [`set_check_mode`] to update the check mode.
    ///
    /// [`set_check_mode`]: ProjectDatabase::set_check_mode
    pub fn check_with_reporter(&self, reporter: &mut dyn ProgressReporter) {
        self.project().check(self, reporter);
    }

    #[tracing::instrument(level = "debug", skip(self))]
    pub fn check_file(&self, file: File) -> Vec<Diagnostic> {
        crate::check_file(self, file)
    }

    /// Set the check mode for the project.
    pub fn set_check_mode(&mut self, mode: CheckMode) {
        if self.project().check_mode(self) != mode {
            tracing::debug!("Updating project to check {mode}");
            self.project().set_check_mode(self).to(mode);
        }
    }

    /// Returns a mutable reference to the system.
    ///
    /// WARNING: Triggers a new revision, canceling other database handles. This can lead to deadlock.
    pub fn system_mut(&mut self) -> &mut dyn System {
        self.trigger_cancellation();

        Arc::get_mut(&mut self.system).expect(
            "ref count should be 1 because `trigger_cancellation` drops all other DB references.",
        )
    }

    /// Returns a [`SalsaMemoryDump`] that can be use to dump Salsa memory usage information
    /// to the CLI after a typechecker run.
    pub fn salsa_memory_dump(&self) -> SalsaMemoryDump {
        let memory_usage = ruff_memory_usage::attach_tracker(StandardTracker::new(), || {
            <dyn salsa::Database>::memory_usage(self)
        });

        let mut ingredients = memory_usage
            .structs
            .into_iter()
            .filter(|ingredient| ingredient.count() > 0)
            .collect::<Vec<_>>();
        let mut memos = memory_usage
            .queries
            .into_iter()
            .filter(|(_, memos)| memos.count() > 0)
            .collect::<Vec<_>>();

        ingredients.sort_by_key(|ingredient| {
            let heap_size = ingredient.heap_size_of_fields().unwrap_or_else(|| {
                // Salsa currently does not expose a way to track the heap size of interned
                // query arguments.
                if !ingredient.debug_name().contains("interned_arguments") {
                    tracing::warn!(
                        "expected `heap_size` to be provided by Salsa struct `{}`",
                        ingredient.debug_name()
                    );
                }

                0
            });

            cmp::Reverse(ingredient.size_of_fields() + heap_size)
        });

        memos.sort_by_key(|(query, memo)| {
            let heap_size = memo.heap_size_of_fields().unwrap_or_else(|| {
                tracing::warn!("expected `heap_size` to be provided by Salsa query `{query}`");
                0
            });

            cmp::Reverse(memo.size_of_fields() + heap_size)
        });

        let mut total_fields = 0;
        let mut total_metadata = 0;
        for ingredient in &ingredients {
            total_fields += ingredient.size_of_fields();
            total_fields += ingredient.heap_size_of_fields().unwrap_or(0);
            total_metadata += ingredient.size_of_metadata();
        }

        let mut total_memo_fields = 0;
        let mut total_memo_metadata = 0;
        for (_, memo) in &memos {
            total_memo_fields += memo.size_of_fields();
            total_memo_fields += memo.heap_size_of_fields().unwrap_or(0);
            total_memo_metadata += memo.size_of_metadata();
        }

        SalsaMemoryDump {
            total_fields,
            total_metadata,
            total_memo_fields,
            total_memo_metadata,
            ingredients,
            memos,
        }
    }
}

impl std::fmt::Debug for ProjectDatabase {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProjectDatabase")
            .field("project", &self.project)
            .field("files", &self.files)
            .field("system", &self.system)
            .finish_non_exhaustive()
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, get_size2::GetSize)]
#[cfg_attr(test, derive(serde::Serialize))]
pub enum CheckMode {
    /// Checks the open files in the project.
    OpenFiles,

    /// Checks all files in the project, ignoring the open file set.
    ///
    /// This includes virtual files, such as those opened in an editor.
    #[default]
    AllFiles,
}

impl fmt::Display for CheckMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CheckMode::OpenFiles => write!(f, "open files"),
            CheckMode::AllFiles => write!(f, "all files"),
        }
    }
}

/// Stores memory usage information.
pub struct SalsaMemoryDump {
    total_fields: usize,
    total_metadata: usize,
    total_memo_fields: usize,
    total_memo_metadata: usize,
    ingredients: Vec<salsa::IngredientInfo>,
    memos: Vec<(&'static str, salsa::IngredientInfo)>,
}

#[expect(clippy::cast_precision_loss)]
fn bytes_to_mb(total: usize) -> f64 {
    total as f64 / 1_000_000.
}

impl SalsaMemoryDump {
    /// Returns a short report that provides total memory usage information.
    pub fn display_short(self) -> impl fmt::Display {
        std::fmt::from_fn(move |f| {
            let SalsaMemoryDump {
                total_fields,
                total_metadata,
                total_memo_fields,
                total_memo_metadata,
                ref ingredients,
                ref memos,
            } = self;

            writeln!(f, "=======SALSA SUMMARY=======")?;

            writeln!(
                f,
                "TOTAL MEMORY USAGE: {:.2}MB",
                bytes_to_mb(
                    total_metadata + total_fields + total_memo_fields + total_memo_metadata
                )
            )?;

            writeln!(
                f,
                "    struct metadata = {:.2}MB",
                bytes_to_mb(total_metadata),
            )?;
            writeln!(f, "    struct fields = {:.2}MB", bytes_to_mb(total_fields))?;
            writeln!(
                f,
                "    memo metadata = {:.2}MB",
                bytes_to_mb(total_memo_metadata),
            )?;
            writeln!(
                f,
                "    memo fields = {:.2}MB",
                bytes_to_mb(total_memo_fields),
            )?;

            writeln!(f, "QUERY COUNT: {}", memos.len())?;
            writeln!(f, "STRUCT COUNT: {}", ingredients.len())?;

            Ok(())
        })
    }

    /// Returns a short report that provides fine-grained memory usage information per
    /// Salsa ingredient.
    pub fn display_full(self) -> impl fmt::Display {
        std::fmt::from_fn(move |f| {
            let SalsaMemoryDump {
                total_fields,
                total_metadata,
                total_memo_fields,
                total_memo_metadata,
                ref ingredients,
                ref memos,
            } = self;

            writeln!(f, "=======SALSA STRUCTS=======")?;

            for ingredient in ingredients {
                let size_of_fields =
                    ingredient.size_of_fields() + ingredient.heap_size_of_fields().unwrap_or(0);

                writeln!(
                    f,
                    "{:<50} metadata={:<8} fields={:<8} count={}",
                    format!("`{}`", ingredient.debug_name()),
                    format!("{:.2}MB", bytes_to_mb(ingredient.size_of_metadata())),
                    format!("{:.2}MB", bytes_to_mb(size_of_fields)),
                    ingredient.count()
                )?;
            }

            writeln!(f, "=======SALSA QUERIES=======")?;

            for (query_fn, memo) in memos {
                let size_of_fields =
                    memo.size_of_fields() + memo.heap_size_of_fields().unwrap_or(0);

                writeln!(f, "`{query_fn} -> {}`", memo.debug_name())?;

                writeln!(
                    f,
                    "    metadata={:<8} fields={:<8} count={}",
                    format!("{:.2}MB", bytes_to_mb(memo.size_of_metadata())),
                    format!("{:.2}MB", bytes_to_mb(size_of_fields)),
                    memo.count()
                )?;
            }

            writeln!(f, "=======SALSA SUMMARY=======")?;
            writeln!(
                f,
                "TOTAL MEMORY USAGE: {:.2}MB",
                bytes_to_mb(
                    total_metadata + total_fields + total_memo_fields + total_memo_metadata
                )
            )?;

            writeln!(
                f,
                "    struct metadata = {:.2}MB",
                bytes_to_mb(total_metadata),
            )?;
            writeln!(f, "    struct fields = {:.2}MB", bytes_to_mb(total_fields))?;
            writeln!(
                f,
                "    memo metadata = {:.2}MB",
                bytes_to_mb(total_memo_metadata),
            )?;
            writeln!(
                f,
                "    memo fields = {:.2}MB",
                bytes_to_mb(total_memo_fields),
            )?;

            Ok(())
        })
    }

    /// Serializes the memory dump to JSON.
    pub fn to_json(&self) -> String {
        #[derive(serde::Serialize)]
        struct MemoryReport {
            total_bytes: usize,
            struct_metadata_bytes: usize,
            struct_fields_bytes: usize,
            memo_metadata_bytes: usize,
            memo_fields_bytes: usize,
            structs: Vec<IngredientReport>,
            queries: Vec<QueryReport>,
        }

        #[derive(serde::Serialize)]
        struct IngredientReport {
            name: String,
            metadata_bytes: usize,
            fields_bytes: usize,
            count: usize,
        }

        #[derive(serde::Serialize)]
        struct QueryReport {
            name: String,
            return_type: String,
            metadata_bytes: usize,
            fields_bytes: usize,
            count: usize,
        }

        let structs = self
            .ingredients
            .iter()
            .map(|ingredient| IngredientReport {
                name: ingredient.debug_name().to_string(),
                metadata_bytes: ingredient.size_of_metadata(),
                fields_bytes: ingredient.size_of_fields()
                    + ingredient.heap_size_of_fields().unwrap_or(0),
                count: ingredient.count(),
            })
            .collect();

        let queries = self
            .memos
            .iter()
            .map(|(query_fn, memo)| QueryReport {
                name: (*query_fn).to_string(),
                return_type: memo.debug_name().to_string(),
                metadata_bytes: memo.size_of_metadata(),
                fields_bytes: memo.size_of_fields() + memo.heap_size_of_fields().unwrap_or(0),
                count: memo.count(),
            })
            .collect();

        let report = MemoryReport {
            total_bytes: self.total_fields
                + self.total_metadata
                + self.total_memo_fields
                + self.total_memo_metadata,
            struct_metadata_bytes: self.total_metadata,
            struct_fields_bytes: self.total_fields,
            memo_metadata_bytes: self.total_memo_metadata,
            memo_fields_bytes: self.total_memo_fields,
            structs,
            queries,
        };

        serde_json::to_string_pretty(&report).expect("Failed to serialize memory report")
    }
}

#[salsa::db]
impl ty_module_resolver::Db for ProjectDatabase {}

#[salsa::db]
impl SemanticDb for ProjectDatabase {
    fn check_file(&self, file: File) -> Vec<Diagnostic> {
        ProjectDatabase::check_file(self, file)
    }

    fn program_file(&self, file: File) -> ProgramFile<'_> {
        let program = match Script::for_file(self, file) {
            None => self.project().program(self),
            Some(script) => script.program(self),
        };

        program.program_file(self, file)
    }

    fn python_version_with_source(&self, file: File) -> &PythonVersionWithSource {
        match Script::for_file(self, file) {
            None => &self.project().program_settings(self).python_version,
            Some(script) => script.python_version_with_source(self),
        }
    }

    fn rule_selection(&self, file: File) -> &RuleSelection {
        let settings = file_settings(self, file);
        settings.rules(self)
    }

    fn lint_registry(&self) -> &LintRegistry {
        ty_python_semantic::default_lint_registry()
    }

    fn analysis_settings(&self, file: File) -> &AnalysisSettings {
        let settings = file_settings(self, file);
        settings.analysis(self)
    }

    fn verbose(&self) -> bool {
        self.project().verbose(self)
    }

    fn is_open_file(&self, file: File) -> bool {
        is_open_file_impl(self, file)
    }

    fn dyn_clone(&self) -> Box<dyn SemanticDb> {
        Box::new(self.clone())
    }
}

#[salsa::db]
impl ty_python_core::Db for ProjectDatabase {
    fn analysis_dialect(&self, _file: File) -> AnalysisDialect {
        self.analysis_dialect
    }

    fn should_check_file(&self, file: File) -> bool {
        // Avoid creating a dependency on the `should_check_file` query for vendored files.
        if file.path(self).is_vendored_path() {
            return false;
        }

        self.project
            .is_some_and(|_| crate::should_check_file(self, file))
    }
}

#[salsa::db]
impl SourceDb for ProjectDatabase {
    fn vendored(&self) -> &VendoredFileSystem {
        match self.analysis_dialect {
            AnalysisDialect::Python => ty_vendored::file_system(),
            AnalysisDialect::SoacStrictV1 => ty_vendored::soac_file_system(),
        }
    }

    fn system(&self) -> &dyn System {
        &*self.system
    }

    fn files(&self) -> &Files {
        &self.files
    }
}

#[salsa::db]
impl salsa::Database for ProjectDatabase {}

#[salsa::db]
impl Db for ProjectDatabase {
    fn project(&self) -> Project {
        self.project.unwrap()
    }

    fn dyn_clone(&self) -> Box<dyn Db> {
        Box::new(self.clone())
    }
}

#[cfg(feature = "format")]
mod format {
    use crate::ProjectDatabase;
    use ruff_db::files::File;
    use ruff_python_formatter::{Db as FormatDb, PyFormatOptions};
    use ty_python_semantic::Db as _;

    #[salsa::db]
    impl FormatDb for ProjectDatabase {
        fn format_options(&self, file: File) -> PyFormatOptions {
            let source_ty = file.source_type(self);
            PyFormatOptions::from_source_type(source_ty)
                .with_target_version(self.program_file(file).python_version(self))
        }
    }
}

#[cfg(any(test, feature = "testing"))]
#[cfg_attr(not(feature = "testing"), expect(unreachable_pub))]
pub(crate) mod testing {
    use std::sync::{Arc, Mutex};

    use ruff_db::Db as SourceDb;
    use ruff_db::diagnostic::Diagnostic;
    use ruff_db::files::{File, FileRootKind, Files};
    use ruff_db::system::{DbWithTestSystem, System, TestSystem};
    use ruff_db::vendored::VendoredFileSystem;
    #[cfg(feature = "testing")]
    use ruff_python_ast::PythonVersion;
    use ty_module_resolver::SearchPathSettings;
    use ty_python_core::ProgramFile;
    use ty_python_core::platform::PythonPlatform;
    use ty_python_core::program::{FallibleStrategy, ProgramSettings};
    #[cfg(feature = "testing")]
    use ty_python_semantic::ProgramEnvironment;
    use ty_python_semantic::lint::{LintRegistry, RuleSelection};
    use ty_python_semantic::{AnalysisSettings, PythonVersionWithSource};

    use crate::db::Db;
    use crate::metadata::settings::file_settings;
    use crate::script::Script;
    use crate::{Project, ProjectMetadata};

    type Events = Arc<Mutex<Vec<salsa::Event>>>;

    #[salsa::db]
    #[derive(Clone)]
    pub struct TestDb {
        storage: salsa::Storage<Self>,
        events: Events,
        files: Files,
        system: TestSystem,
        vendored: VendoredFileSystem,
        project: Option<Project>,
    }

    impl TestDb {
        pub fn new(project: ProjectMetadata) -> Self {
            let events = Events::default();
            let mut db = Self {
                storage: salsa::Storage::new(Some(Box::new({
                    let events = events.clone();
                    move |event| {
                        let mut events = events.lock().unwrap();
                        events.push(event);
                    }
                }))),
                system: TestSystem::default(),
                vendored: ty_vendored::file_system().clone(),
                files: Files::default(),
                events,
                project: None,
            };

            let (settings, settings_diagnostics) = project
                .to_merged_options()
                .to_settings(&db, &FallibleStrategy)
                .unwrap();
            let root = project.root().to_path_buf();
            db.system
                .memory_file_system()
                .create_directory_all(&root)
                .expect("create project root");
            let search_paths = SearchPathSettings::new(vec![root.clone()])
                .to_search_paths(db.system(), db.vendored(), &FallibleStrategy)
                .expect("Valid search path settings");

            db.files().try_add_root(&db, &root, FileRootKind::Project);

            let program_settings = ProgramSettings {
                python_version: PythonVersionWithSource::default(),
                python_platform: PythonPlatform::default(),
                search_paths,
            };
            let project = Project::from_metadata(
                &db,
                project,
                settings,
                program_settings,
                settings_diagnostics,
            );
            db.project = Some(project);
            db
        }

        #[cfg(feature = "testing")]
        pub fn set_python_version(&mut self, python_version: PythonVersion) {
            let program = self.project().program(self);
            let settings = ProgramSettings {
                python_version: PythonVersionWithSource {
                    source: ty_python_semantic::PythonVersionSource::Default,
                    version: python_version,
                },
                python_platform: program.python_platform(self).clone(),
                search_paths: program.search_paths(self).clone(),
            };
            self.project().update_program(self, settings);
        }
    }

    impl TestDb {
        #[cfg(feature = "testing")]
        pub fn program_environment(&self) -> ProgramEnvironment<'_> {
            ProgramEnvironment::from_program(self.project().program(self))
        }

        /// Takes the salsa events.
        pub fn take_salsa_events(&mut self) -> Vec<salsa::Event> {
            let mut events = self.events.lock().unwrap();

            std::mem::take(&mut *events)
        }
    }

    impl DbWithTestSystem for TestDb {
        fn test_system(&self) -> &TestSystem {
            &self.system
        }

        fn test_system_mut(&mut self) -> &mut TestSystem {
            &mut self.system
        }
    }

    #[salsa::db]
    impl SourceDb for TestDb {
        fn vendored(&self) -> &VendoredFileSystem {
            &self.vendored
        }

        fn system(&self) -> &dyn System {
            &self.system
        }

        fn files(&self) -> &Files {
            &self.files
        }
    }

    #[salsa::db]
    impl ty_module_resolver::Db for TestDb {}

    #[salsa::db]
    impl ty_python_core::Db for TestDb {
        fn should_check_file(&self, file: ruff_db::files::File) -> bool {
            crate::should_check_file(self, file)
        }
    }

    #[salsa::db]
    impl ty_python_semantic::Db for TestDb {
        fn program_file(&self, file: File) -> ProgramFile<'_> {
            let program = match Script::for_file(self, file) {
                None => self.project().program(self),
                Some(script) => script.program(self),
            };

            program.program_file(self, file)
        }

        fn python_version_with_source(&self, file: File) -> &PythonVersionWithSource {
            match Script::for_file(self, file) {
                None => &self.project().program_settings(self).python_version,
                Some(script) => script.python_version_with_source(self),
            }
        }

        #[inline]
        fn check_file(&self, file: File) -> Vec<Diagnostic> {
            crate::check_file(self, file)
        }

        fn rule_selection(&self, file: ruff_db::files::File) -> &RuleSelection {
            file_settings(self, file).rules(self)
        }

        fn lint_registry(&self) -> &LintRegistry {
            ty_python_semantic::default_lint_registry()
        }

        fn analysis_settings(&self, file: ruff_db::files::File) -> &AnalysisSettings {
            file_settings(self, file).analysis(self)
        }

        fn verbose(&self) -> bool {
            false
        }

        fn is_open_file(&self, file: File) -> bool {
            super::is_open_file_impl(self, file)
        }

        fn dyn_clone(&self) -> Box<dyn ty_python_semantic::Db> {
            Box::new(self.clone())
        }
    }

    #[salsa::db]
    impl Db for TestDb {
        fn project(&self) -> Project {
            self.project.unwrap()
        }

        fn dyn_clone(&self) -> Box<dyn Db> {
            Box::new(self.clone())
        }
    }

    #[salsa::db]
    impl salsa::Database for TestDb {}
}

#[cfg(test)]
mod tests {
    use ruff_db::Db as _;
    use ruff_db::files::{FileRootKind, system_path_to_file};
    use ruff_db::parsed::parsed_module;
    use ruff_db::source::source_text;
    use ruff_db::system::{SystemPathBuf, TestSystem};
    use ruff_python_ast::PythonVersion;
    use ruff_python_parser::semantic_errors::SemanticSyntaxErrorKind;
    use ty_module_resolver::list_modules;
    use ty_python_core::{AnalysisDialect, AnalysisPolicy, ProgramFile, semantic_index};
    use ty_python_semantic::types::{KnownClass, Type};
    use ty_python_semantic::{Db as _, HasType, SemanticModel, effective_analysis_settings};

    use crate::{Db as _, ProjectDatabase, ProjectMetadata};

    #[test]
    fn frozen_inputs_support_a_one_shot_check() -> anyhow::Result<()> {
        let system = TestSystem::default();
        let project = SystemPathBuf::from("/project");
        system
            .memory_file_system()
            .write_file_all(project.join("main.py"), "x: int = 'not an int'")?;

        let metadata = ProjectMetadata::discover(&project, &system)?;
        let mut db = ProjectDatabase::fallible(metadata, system)?;
        db.freeze();

        assert_eq!(db.check().len(), 1);

        Ok(())
    }

    #[test]
    fn search_root_registration() -> anyhow::Result<()> {
        let system = TestSystem::default();
        let project = SystemPathBuf::from("/project");
        let project_src = project.join("src");
        let external = SystemPathBuf::from("/external");
        let venv = project.join(".venv");

        system.memory_file_system().write_files_all([
            (
                project.join("ty.toml"),
                r#"
                [environment]
                root = ["src", "../external"]
                extra-paths = [".venv"]
                "#,
            ),
            (project_src.join("foo.py"), ""),
            (external.join("bar.py"), ""),
            (venv.join("baz.py"), ""),
        ])?;

        let metadata = ProjectMetadata::discover(&project, &system)?;
        let db = ProjectDatabase::fallible(metadata, system)?;

        let modules = list_modules(&db, db.project().program(&db).resolver_environment(&db));
        assert!(
            modules
                .iter()
                .any(|module| module.name(&db).as_str() == "bar")
        );

        let project_src_root = db
            .files()
            .root(&db, &project_src)
            .expect("project source file root");
        assert_eq!(project_src_root.path(&db), &*project);
        assert_eq!(
            project_src_root.kind_at_time_of_creation(&db),
            FileRootKind::Project
        );

        let external_root = db
            .files()
            .root(&db, &external)
            .expect("external first-party file root");
        assert_eq!(external_root.path(&db), &*external);
        assert_eq!(
            external_root.kind_at_time_of_creation(&db),
            FileRootKind::SearchPath
        );

        let venv_root = db.files().root(&db, &venv).expect("virtualenv file root");
        assert_eq!(venv_root.path(&db), &*venv);
        assert_eq!(
            venv_root.kind_at_time_of_creation(&db),
            FileRootKind::SearchPath
        );

        Ok(())
    }

    fn dialect_db(
        dialect: AnalysisDialect,
        python_version: &str,
        options: &str,
        source: &str,
    ) -> anyhow::Result<ProjectDatabase> {
        let system = TestSystem::default();
        let project = SystemPathBuf::from("/project");
        let config = format!("[environment]\npython-version = \"{python_version}\"\n{options}");
        system.memory_file_system().write_files_all([
            (project.join("ty.toml"), config.as_str()),
            (project.join("main.py"), source),
        ])?;
        let metadata = ProjectMetadata::discover(&project, &system)?;
        match dialect {
            AnalysisDialect::Python => ProjectDatabase::fallible(metadata, system),
            AnalysisDialect::SoacStrictV1 => {
                ProjectDatabase::fallible_with_analysis_dialect(metadata, system, dialect)
            }
        }
    }

    fn main_file(db: &ProjectDatabase) -> ProgramFile<'_> {
        db.program_file(system_path_to_file(db, "/project/main.py").unwrap())
    }

    fn guarded_expression_type<'db>(db: &'db ProjectDatabase, function_name: &str) -> Type<'db> {
        let file = main_file(db);
        let parsed = parsed_module(db, file.python_file(db)).load(db);
        let function = parsed
            .syntax()
            .body
            .iter()
            .filter_map(|stmt| stmt.as_function_def_stmt())
            .find(|function| function.name.as_str() == function_name)
            .unwrap();
        let guard = function.body[0].as_if_stmt().unwrap();
        let expression = &guard.body[0].as_expr_stmt().unwrap().value;
        expression
            .inferred_type(&SemanticModel::new(db, file))
            .unwrap()
    }

    #[test]
    fn soac_future_requires_explicit_dialect_and_preserves_source() -> anyhow::Result<()> {
        let source = "\"\"\"Unicode δ docstring.\"\"\"\nfrom __future__ import strict, annotations\nflag: int = strict.compiler_flag\n";
        let ordinary = dialect_db(AnalysisDialect::Python, "3.15", "", source)?;
        let ordinary_file = main_file(&ordinary);
        let errors = semantic_index(&ordinary, ordinary_file).semantic_syntax_errors();
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].kind,
            SemanticSyntaxErrorKind::FutureFeatureNotDefined("strict".to_owned())
        );

        let soac = dialect_db(AnalysisDialect::SoacStrictV1, "3.15", "", source)?;
        let file = main_file(&soac);
        assert!(
            semantic_index(&soac, file)
                .semantic_syntax_errors()
                .is_empty()
        );
        assert!(soac.check_file(file.file(&soac)).is_empty());
        assert_eq!(source_text(&soac, file.file(&soac)).as_str(), source);
        let parsed = parsed_module(&soac, file.python_file(&soac)).load(&soac);
        let import = parsed.syntax().body[1].as_import_from_stmt().unwrap();
        assert_eq!(import.module.as_deref(), Some("__future__"));
        assert_eq!(import.names[0].name.as_str(), "strict");
        assert_eq!(import.names[1].name.as_str(), "annotations");
        assert_eq!(import.names[0].range, errors[0].range);
        let range = import.names[0].range;
        assert_eq!(
            &source[usize::from(range.start())..usize::from(range.end())],
            "strict"
        );
        assert_eq!(
            file.analysis_policy(&soac),
            AnalysisPolicy {
                dialect: AnalysisDialect::SoacStrictV1,
                python_version: PythonVersion::PY315,
            }
        );
        Ok(())
    }

    #[test]
    fn soac_future_keeps_placement_and_unknown_feature_errors() -> anyhow::Result<()> {
        for (source, expected) in [
            (
                "value = 1\nfrom __future__ import strict\n",
                SemanticSyntaxErrorKind::LateFutureImport,
            ),
            (
                "def f():\n    from __future__ import strict\n",
                SemanticSyntaxErrorKind::LateFutureImport,
            ),
            (
                "lazy from __future__ import strict\n",
                SemanticSyntaxErrorKind::LazyFutureImport,
            ),
            (
                "from __future__ import strict, unrecognized\n",
                SemanticSyntaxErrorKind::FutureFeatureNotDefined("unrecognized".to_owned()),
            ),
        ] {
            let db = dialect_db(AnalysisDialect::SoacStrictV1, "3.15", "", source)?;
            let errors = semantic_index(&db, main_file(&db)).semantic_syntax_errors();
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert_eq!(errors[0].kind, expected);
        }
        Ok(())
    }

    #[test]
    fn soac_future_stub_does_not_leak_into_ordinary_analysis() -> anyhow::Result<()> {
        let source = "import __future__\nsoac_feature = __future__.strict\npython_feature = __future__.annotations\n";
        for dialect in [AnalysisDialect::Python, AnalysisDialect::SoacStrictV1] {
            let db = dialect_db(dialect, "3.15", "", source)?;
            let file = main_file(&db);
            let parsed = parsed_module(&db, file.python_file(&db)).load(&db);
            let model = SemanticModel::new(&db, file);
            let types: Vec<_> = parsed.syntax().body[1..]
                .iter()
                .map(|stmt| {
                    stmt.as_assign_stmt()
                        .unwrap()
                        .value
                        .inferred_type(&model)
                        .unwrap()
                })
                .collect();
            assert_ne!(types[1], Type::unknown());
            match dialect {
                AnalysisDialect::Python => {
                    assert_eq!(types[0], Type::unknown());
                    assert!(!db.check_file(file.file(&db)).is_empty());
                }
                AnalysisDialect::SoacStrictV1 => {
                    assert_eq!(types[0], types[1]);
                    assert!(db.check_file(file.file(&db)).is_empty());
                }
            }
        }
        Ok(())
    }

    #[test]
    fn soac_configured_python_315_drives_parser_and_typeshed() -> anyhow::Result<()> {
        let source = "lazy import math\nimport sys\nbits: int = sys.abi_info.pointer_bits\n";
        for dialect in [AnalysisDialect::Python, AnalysisDialect::SoacStrictV1] {
            let py315 = dialect_db(dialect, "3.15", "", source)?;
            let file = main_file(&py315);
            assert_eq!(file.python_version(&py315), PythonVersion::PY315);
            assert_eq!(
                file.analysis_policy(&py315).python_version,
                PythonVersion::PY315
            );
            let parsed = parsed_module(&py315, file.python_file(&py315)).load(&py315);
            assert!(parsed.unsupported_syntax_errors().is_empty());
            assert!(
                semantic_index(&py315, file)
                    .semantic_syntax_errors()
                    .is_empty()
            );
            assert!(py315.check_file(file.file(&py315)).is_empty());

            let py314 = dialect_db(dialect, "3.14", "", source)?;
            let file = main_file(&py314);
            assert_eq!(file.python_version(&py314), PythonVersion::PY314);
            let parsed = parsed_module(&py314, file.python_file(&py314)).load(&py314);
            assert!(!parsed.unsupported_syntax_errors().is_empty());
            assert!(!py314.check_file(file.file(&py314)).is_empty());
        }
        // latest_ty is a fallback, not the maximum accepted configured version.
        assert_eq!(PythonVersion::latest_ty(), PythonVersion::PY314);
        Ok(())
    }

    #[test]
    fn soac_effective_settings_override_unsafe_project_and_file_options() -> anyhow::Result<()> {
        let source = "class Covariant[T]:\n    def get(self) -> T:\n        raise NotImplementedError\n\ndef equality(value: int):\n    if value == 1:\n        value\n\ndef generic(value: object):\n    if isinstance(value, Covariant):\n        value.get()\n";
        for options in [
            "[analysis]\nstrict-equality-semantics = false\nstrict-generic-narrowing = false\n",
            "[analysis]\nstrict-equality-semantics = true\nstrict-generic-narrowing = true\n[[overrides]]\ninclude = [\"main.py\"]\n[overrides.analysis]\nstrict-equality-semantics = false\nstrict-generic-narrowing = false\n",
        ] {
            for dialect in [AnalysisDialect::Python, AnalysisDialect::SoacStrictV1] {
                let db = dialect_db(dialect, "3.15", options, source)?;
                let file = main_file(&db);
                let raw = db.analysis_settings(file.file(&db));
                assert!(!raw.strict_equality_semantics);
                assert!(!raw.strict_generic_narrowing);
                let effective = effective_analysis_settings(&db, file.file(&db));
                let equality = guarded_expression_type(&db, "equality");
                let generic = guarded_expression_type(&db, "generic");
                match dialect {
                    AnalysisDialect::Python => {
                        assert_eq!(effective, raw);
                        assert!(matches!(equality, Type::LiteralValue(_)));
                        assert_eq!(generic, Type::unknown());
                    }
                    AnalysisDialect::SoacStrictV1 => {
                        assert!(effective.strict_equality_semantics);
                        assert!(effective.strict_generic_narrowing);
                        let env = SemanticModel::new(&db, file).program_environment();
                        assert_eq!(equality, KnownClass::Int.to_instance(&db, &env));
                        assert_eq!(generic, KnownClass::Object.to_instance(&db, &env));
                    }
                }
            }
        }
        Ok(())
    }

    #[test]
    fn soac_script_policy_reports_real_version_and_cannot_weaken_analysis() -> anyhow::Result<()> {
        let source = "# /// script\n# requires-python = \">=3.14\"\n# [tool.ty.analysis]\n# strict-equality-semantics = false\n# strict-generic-narrowing = false\n# ///\nfrom __future__ import strict\ndef equality(value: int):\n    if value == 1:\n        value\n";
        let db = dialect_db(AnalysisDialect::SoacStrictV1, "3.15", "", source)?;
        let file = main_file(&db);
        assert_eq!(
            file.analysis_policy(&db),
            AnalysisPolicy {
                dialect: AnalysisDialect::SoacStrictV1,
                python_version: PythonVersion::PY314,
            }
        );
        let effective = effective_analysis_settings(&db, file.file(&db));
        assert!(effective.strict_equality_semantics);
        assert!(effective.strict_generic_narrowing);
        let env = SemanticModel::new(&db, file).program_environment();
        assert_eq!(
            guarded_expression_type(&db, "equality"),
            KnownClass::Int.to_instance(&db, &env)
        );
        Ok(())
    }
}
