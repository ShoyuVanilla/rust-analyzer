//! Read `.cargo/config.toml` as a JSON object
use paths::{AbsPathBuf, Utf8Path, Utf8PathBuf};
use rustc_hash::FxHashMap;
use toml::{
    Spanned,
    de::{DeTable, DeValue},
};
use toolchain::Tool;

use crate::{ManifestPath, Sysroot, utf8_stdout};

pub(crate) type CargoConfigFile = serde_json::Map<String, serde_json::Value>;

pub(crate) struct CargoConfigFileReader<'a> {
    toml_str: &'a str,
    line_ends: Vec<usize>,
    toml: Spanned<DeTable<'a>>,
}

impl<'a> CargoConfigFileReader<'a> {
    pub(crate) fn read(
        manifest: &ManifestPath,
        extra_env: &FxHashMap<String, Option<String>>,
        sysroot: &Sysroot,
    ) -> Option<Self> {
        let mut cargo_config = sysroot.tool(Tool::Cargo, manifest.parent(), extra_env);
        cargo_config
            .args(["-Z", "unstable-options", "config", "get", "--format", "toml", "--show-origin"])
            .env("RUSTC_BOOTSTRAP", "1");
        if manifest.is_rust_manifest() {
            cargo_config.arg("-Zscript");
        }

        tracing::debug!("Discovering cargo config by {cargo_config:?}");
        let toml_str = utf8_stdout(&mut cargo_config)
            .inspect(|toml| {
                tracing::debug!("Discovered cargo config: {toml:?}");
            })
            .inspect_err(|err| {
                tracing::debug!("Failed to discover cargo config: {err:?}");
            })
            .ok()?;
        let toml = DeTable::parse(&toml_str)
            .inspect_err(|err| tracing::debug!("Failed to parse cargo config into toml: {err:?}"))
            .ok()?;
        let line_ends = toml_str.lines().fold(vec![], |mut acc, l| {
            acc.push(acc.last().copied().unwrap_or(0_usize) + l.len());
            acc
        });

        todo!()
        // Some(CargoConfigFile2 { toml_str, toml, line_ends })
    }

    pub(crate) fn new(toml_str: &'a str) -> Option<Self> {
        let toml = DeTable::parse(&toml_str)
            .inspect_err(|err| tracing::debug!("Failed to parse cargo config into toml: {err:?}"))
            .ok()?;
        let line_ends = toml_str.lines().fold(vec![], |mut acc, l| {
            acc.push(acc.last().copied().unwrap_or(0_usize) + l.len());
            acc
        });

        Some(CargoConfigFileReader { toml_str, toml, line_ends })
    }

    fn get_spanned(
        &self,
        accessor: impl IntoIterator<Item = &'a str>,
    ) -> Option<&Spanned<DeValue<'a>>> {
        let mut keys = accessor.into_iter();
        let mut val = self.toml.get_ref().get(keys.next()?)?;
        for key in keys {
            let DeValue::Table(map) = val.get_ref() else { return None };
            val = map.get(key)?;
        }
        Some(val)
    }

    pub(crate) fn get(&self, accessor: impl IntoIterator<Item = &'a str>) -> Option<&DeValue<'a>> {
        self.get_spanned(accessor).map(Spanned::get_ref)
    }

    pub(crate) fn get_with_origin(
        &'a self,
        accessor: impl IntoIterator<Item = &'a str>,
    ) -> Option<(&'a DeValue<'a>, Option<AbsPathBuf>)> {
        let val = self.get_spanned(accessor)?;
        let span = val.span();
        for &end in &self.line_ends {
            if end < span.end {
                continue;
            }

            // table.key = "value" # [ROOT]/home/.cargo/config.toml
            //                   |                                |
            //                   span.end                         end
            let origin_path =
                &self.toml_str[span.end..end].trim_start().strip_prefix('#').and_then(|path| {
                    let path = path.trim();
                    if path.starts_with("environment variable") { None } else { Some(path) }
                });

            return Some((
                val.get_ref(),
                origin_path.and_then(|path| Utf8PathBuf::from(path).try_into().ok()),
            ));
        }

        None
    }
}

pub(crate) fn read(
    manifest: &ManifestPath,
    extra_env: &FxHashMap<String, Option<String>>,
    sysroot: &Sysroot,
) -> Option<CargoConfigFile> {
    let mut cargo_config = sysroot.tool(Tool::Cargo, manifest.parent(), extra_env);
    cargo_config
        .args(["-Z", "unstable-options", "config", "get", "--format", "json"])
        .env("RUSTC_BOOTSTRAP", "1");
    if manifest.is_rust_manifest() {
        cargo_config.arg("-Zscript");
    }

    tracing::debug!("Discovering cargo config by {:?}", cargo_config);
    let json: serde_json::Map<String, serde_json::Value> = utf8_stdout(&mut cargo_config)
        .inspect(|json| {
            tracing::debug!("Discovered cargo config: {:?}", json);
        })
        .inspect_err(|err| {
            tracing::debug!("Failed to discover cargo config: {:?}", err);
        })
        .ok()
        .and_then(|stdout| serde_json::from_str(&stdout).ok())?;

    Some(json)
}

pub(crate) fn make_lockfile_copy(
    lockfile_path: &Utf8Path,
) -> Option<(temp_dir::TempDir, Utf8PathBuf)> {
    let temp_dir = temp_dir::TempDir::with_prefix("rust-analyzer").ok()?;
    let target_lockfile = temp_dir.path().join("Cargo.lock").try_into().ok()?;
    match std::fs::copy(lockfile_path, &target_lockfile) {
        Ok(_) => {
            tracing::debug!("Copied lock file from `{}` to `{}`", lockfile_path, target_lockfile);
            Some((temp_dir, target_lockfile))
        }
        // lockfile does not yet exist, so we can just create a new one in the temp dir
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Some((temp_dir, target_lockfile)),
        Err(e) => {
            tracing::warn!(
                "Failed to copy lock file from `{lockfile_path}` to `{target_lockfile}`: {e}",
            );
            None
        }
    }
}

#[test]
fn foobar() {
    let s = r##"
alias.codegen = "run --package xtask --bin xtask -- codegen" # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
alias.dist = "run --package xtask --bin xtask -- dist" # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
alias.lint = "clippy --all-targets -- --cap-lints warn" # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
alias.qt = "tq" # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
alias.tq = "test -- -q" # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
alias.xtask = "run --package xtask --bin xtask --" # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
env.CARGO_WORKSPACE_DIR.relative = true # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
env.CARGO_WORKSPACE_DIR.value = "" # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
env.foo = [
    "x", # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
    "yz", # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
]
target.x86_64-pc-windows-msvc.linker = "rust-lld" # /home/shoyu/projects/rust-analyzer-git/.cargo/config.toml
"##;
    let x = DeTable::parse(s).unwrap();
    dbg!(&x);
}
