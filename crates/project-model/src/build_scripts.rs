//! Workspace information we get from cargo consists of two pieces. The first is
//! the output of `cargo metadata`. The second is the output of running
//! `build.rs` files (`OUT_DIR` env var, extra cfg flags) and compiling proc
//! macro.
//!
//! This module implements this second part. We use "build script" terminology
//! here, but it covers procedural macros as well.

use std::{
    cell::RefCell,
    io,
    path::PathBuf,
    process::{Command, Stdio},
};

use cargo_metadata::{camino::Utf8Path, Message};
use la_arena::ArenaMap;
use paths::AbsPathBuf;
use rustc_hash::FxHashMap;
use serde::Deserialize;

use crate::{cfg_flag::CfgFlag, CargoConfig, CargoWorkspace, Package};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct WorkspaceBuildScripts {
    pub(crate) outputs: ArenaMap<Package, BuildScriptOutput>,
    error: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct BuildScriptOutput {
    /// List of config flags defined by this package's build script.
    pub(crate) cfgs: Vec<CfgFlag>,
    /// List of cargo-related environment variables with their value.
    ///
    /// If the package has a build script which defines environment variables,
    /// they can also be found here.
    pub(crate) envs: Vec<(String, String)>,
    /// Directory where a build script might place its output.
    pub(crate) out_dir: Option<AbsPathBuf>,
    /// Path to the proc-macro library file if this package exposes proc-macros.
    pub(crate) proc_macro_dylib_path: Option<AbsPathBuf>,
}

impl WorkspaceBuildScripts {
    fn build_command(config: &CargoConfig) -> Command {
        if let Some([program, args @ ..]) = config.run_build_script_command.as_deref() {
            let mut cmd = Command::new(program);
            cmd.args(args);
            return cmd;
        }

        let mut cmd = Command::new(toolchain::cargo());

        cmd.args(&["check", "--quiet", "--workspace", "--message-format=json"]);

        // --all-targets includes tests, benches and examples in addition to the
        // default lib and bins. This is an independent concept from the --targets
        // flag below.
        cmd.arg("--all-targets");

        if let Some(target) = &config.target {
            cmd.args(&["--target", target]);
        }

        if config.all_features {
            cmd.arg("--all-features");
        } else {
            if config.no_default_features {
                cmd.arg("--no-default-features");
            }
            if !config.features.is_empty() {
                cmd.arg("--features");
                cmd.arg(config.features.join(" "));
            }
        }

        cmd
    }
    pub(crate) fn run(
        config: &CargoConfig,
        workspace: &CargoWorkspace,
        progress: &dyn Fn(String),
    ) -> io::Result<WorkspaceBuildScripts> {
        let mut cmd = Self::build_command(config);

        if config.wrap_rustc_in_build_scripts {
            // Setup RUSTC_WRAPPER to point to `rust-analyzer` binary itself. We use
            // that to compile only proc macros and build scripts during the initial
            // `cargo check`.
            let myself = std::env::current_exe()?;
            cmd.env("RUSTC_WRAPPER", myself);
            cmd.env("RA_RUSTC_WRAPPER", "1");
        }

        cmd.current_dir(workspace.workspace_root());

        cmd.stdout(Stdio::piped()).stderr(Stdio::piped()).stdin(Stdio::null());

        let mut res = WorkspaceBuildScripts::default();
        // NB: Cargo.toml could have been modified between `cargo metadata` and
        // `cargo check`. We shouldn't assume that package ids we see here are
        // exactly those from `config`.
        let mut by_id: FxHashMap<String, Package> = FxHashMap::default();

        for package in workspace.packages() {
            res.outputs.insert(package, BuildScriptOutput::default());
            by_id.insert(workspace[package].id.clone(), package);
        }

        let errors = RefCell::new(String::new());
        let push_err = |err: &str| {
            let mut e = errors.borrow_mut();
            e.push_str(err);
            e.push('\n');
        };
        let output = stdx::process::streaming_output(
            cmd,
            &mut |line| {
                // Copy-pasted from existing cargo_metadata. It seems like we
                // should be using serde_stacker here?
                let mut deserializer = serde_json::Deserializer::from_str(line);
                deserializer.disable_recursion_limit();
                let message = Message::deserialize(&mut deserializer)
                    .unwrap_or_else(|_| Message::TextLine(line.to_string()));

                match message {
                    Message::BuildScriptExecuted(message) => {
                        let package = match by_id.get(&message.package_id.repr) {
                            Some(&it) => it,
                            None => return,
                        };
                        let cfgs = {
                            let mut acc = Vec::new();
                            for cfg in message.cfgs {
                                match cfg.parse::<CfgFlag>() {
                                    Ok(it) => acc.push(it),
                                    Err(err) => {
                                        push_err(&format!(
                                            "invalid cfg from cargo-metadata: {}",
                                            err
                                        ));
                                        return;
                                    }
                                };
                            }
                            acc
                        };
                        let package_build_data = &mut res.outputs[package];
                        // cargo_metadata crate returns default (empty) path for
                        // older cargos, which is not absolute, so work around that.
                        if !message.out_dir.as_str().is_empty() {
                            let out_dir =
                                AbsPathBuf::assert(PathBuf::from(message.out_dir.into_os_string()));
                            package_build_data.out_dir = Some(out_dir);
                            package_build_data.cfgs = cfgs;
                        }

                        package_build_data.envs = message.env;
                    }
                    Message::CompilerArtifact(message) => {
                        let package = match by_id.get(&message.package_id.repr) {
                            Some(it) => *it,
                            None => return,
                        };

                        progress(format!("metadata {}", message.target.name));

                        if message.target.kind.iter().any(|k| k == "proc-macro") {
                            // Skip rmeta file
                            if let Some(filename) =
                                message.filenames.iter().find(|name| is_dylib(name))
                            {
                                let filename = AbsPathBuf::assert(PathBuf::from(&filename));
                                res.outputs[package].proc_macro_dylib_path = Some(filename);
                            }
                        }
                    }
                    Message::CompilerMessage(message) => {
                        progress(message.target.name);

                        if let Some(diag) = message.message.rendered.as_deref() {
                            push_err(diag);
                        }
                    }
                    Message::BuildFinished(_) => {}
                    Message::TextLine(_) => {}
                    _ => {}
                }
            },
            &mut |line| {
                push_err(line);
            },
        )?;

        for package in workspace.packages() {
            let package_build_data = &mut res.outputs[package];
            tracing::info!(
                "{} BuildScriptOutput: {:?}",
                workspace[package].manifest.parent().display(),
                package_build_data,
            );
            // inject_cargo_env(package, package_build_data);
            if let Some(out_dir) = &package_build_data.out_dir {
                // NOTE: cargo and rustc seem to hide non-UTF-8 strings from env! and option_env!()
                if let Some(out_dir) = out_dir.as_os_str().to_str().map(|s| s.to_owned()) {
                    package_build_data.envs.push(("OUT_DIR".to_string(), out_dir));
                }
            }
        }

        let mut errors = errors.into_inner();
        if !output.status.success() {
            if errors.is_empty() {
                errors = "cargo check failed".to_string();
            }
            res.error = Some(errors);
        }

        Ok(res)
    }

    pub fn error(&self) -> Option<&str> {
        self.error.as_deref()
    }
}

// FIXME: File a better way to know if it is a dylib.
fn is_dylib(path: &Utf8Path) -> bool {
    match path.extension().map(|e| e.to_string().to_lowercase()) {
        None => false,
        Some(ext) => matches!(ext.as_str(), "dll" | "dylib" | "so"),
    }
}
