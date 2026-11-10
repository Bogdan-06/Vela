//! External assembler/linker integration. GCC only consumes generated assembly.
use crate::codegen::Target;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
pub struct Scratch {
    pub path: PathBuf,
}
impl Scratch {
    pub fn new() -> Result<Self, String> {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| e.to_string())?
            .as_nanos();
        for _ in 0..100 {
            let path = std::env::temp_dir().join(format!(
                "vela-{}-{}-{}",
                std::process::id(),
                now,
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e.to_string()),
            }
        }
        Err("could not create temporary build directory".into())
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[derive(Debug)]
pub struct BuildOutcome {
    pub cached: bool,
}
pub struct BuildOptions {
    pub target: Target,
    pub cc: String,
    pub cache: bool,
}
impl BuildOptions {
    pub fn host() -> Result<Self, String> {
        Ok(Self {
            target: Target::host()?,
            cc: std::env::var("VELA_CC").unwrap_or_else(|_| "gcc".into()),
            cache: true,
        })
    }
}

pub fn executable_name(target: Target) -> &'static str {
    match target {
        Target::Windows => "program.exe",
        Target::Linux => "program",
    }
}
fn compiler_identity(options: &BuildOptions) -> Result<String, String> {
    let version = Command::new(&options.cc)
        .arg("--version")
        .output()
        .map_err(|e| {
            format!(
                "cannot start assembler/linker '{}': {e}; install GCC/MinGW or set VELA_CC",
                options.cc
            )
        })?;
    if !version.status.success() {
        return Err("assembler/linker --version failed".into());
    }
    let machine = Command::new(&options.cc)
        .arg("-dumpmachine")
        .output()
        .map_err(|e| e.to_string())?;
    if !machine.status.success() {
        return Err("assembler/linker -dumpmachine failed".into());
    }
    let triple = String::from_utf8_lossy(&machine.stdout);
    let matches_os = match options.target {
        Target::Windows => triple.contains("mingw") || triple.contains("windows"),
        Target::Linux => triple.contains("linux"),
    };
    if !triple.trim().starts_with("x86_64") || !matches_os {
        return Err(format!(
            "assembler/linker target '{}' does not match requested x86-64 {:?} target",
            triple.trim(),
            options.target
        ));
    }
    Ok(format!(
        "{}\n{}\n{}",
        options.cc,
        String::from_utf8_lossy(&version.stdout),
        triple
    ))
}

/// Cache lookup uses a hash only as a directory index; full key bytes must match.
/// This caches assembly/link results, not frontend queries or individual modules.
pub fn build_assembly(
    assembly: &str,
    destination: &Path,
    options: &BuildOptions,
) -> Result<BuildOutcome, String> {
    let identity = compiler_identity(options)?;
    let key = format!(
        "vela-native-cache-v1\n{identity}\n{:?}\n{assembly}",
        options.target
    );
    let mut hash = 0xcbf29ce484222325u64;
    for byte in key.bytes() {
        hash = (hash ^ u64::from(byte)).wrapping_mul(0x100000001b3);
    }
    let cache = std::env::current_dir()
        .map_err(|e| e.to_string())?
        .join(".vela-cache")
        .join(format!("{hash:016x}"));
    let cached_binary = cache.join(executable_name(options.target));
    if options.cache
        && fs::read(cache.join("key")).ok().as_deref() == Some(key.as_bytes())
        && cached_binary.is_file()
    {
        copy_output(&cached_binary, destination)?;
        return Ok(BuildOutcome { cached: true });
    }
    let scratch = Scratch::new()?;
    let input = scratch.path.join("program.s");
    let binary = scratch.path.join(executable_name(options.target));
    fs::write(&input, assembly).map_err(|e| e.to_string())?;
    let output = Command::new(&options.cc)
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .map_err(|e| format!("cannot start assembler/linker: {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "native assembler/linker failed ({}):\n{}{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if options.cache {
        // A cache write failure cannot turn a successful compilation into a failure.
        if fs::create_dir_all(&cache).is_ok() && fs::copy(&binary, &cached_binary).is_ok() {
            let _ = fs::write(cache.join("key"), key);
        }
    }
    // Publish the linker-created inode directly when possible. Besides avoiding
    // copying, this permits replacing an executable currently running on Unix
    // and avoids transient ETXTBSY races from write handles during parallel builds.
    if let Some(parent) = destination.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    if fs::rename(&binary, destination).is_err() {
        // The temporary directory and requested output may be on different drives.
        copy_output(&binary, destination)?;
    }
    Ok(BuildOutcome { cached: false })
}
fn copy_output(from: &Path, to: &Path) -> Result<(), String> {
    if let Some(parent) = to.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    fs::copy(from, to).map_err(|e| format!("cannot write '{}': {e}", to.display()))?;
    Ok(())
}
