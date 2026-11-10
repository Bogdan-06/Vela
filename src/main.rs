use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::Instant;
use vela::{
    codegen::Target,
    driver::{self, BuildOptions, Scratch},
};

const HELP: &str = concat!("Vela ", env!("CARGO_PKG_VERSION"), " — experimental native x86-64 compiler\n\nUsage: vela <check|ir|cfg|asm|build|run> <file.vela> [options]\n\n  -o, --output PATH     Output executable (build) or text file (asm/ir)\n  --release            Fold constants and eliminate unused pure CFG definitions\n  --target windows|linux  Assembly/assembler target (default: host)\n  --cc PATH            GCC-compatible assembler/linker (or VELA_CC)\n  --no-cache           Disable assembly/link artifact cache\n  --timings            Report grouped compiler/driver wall time to stderr\n  -h, --help           Show this help\n  --version            Show compiler version\n\nExamples:\n  vela run examples/hello.vela\n  vela build examples/loops.vela --release -o loops.exe\n  vela asm examples/fibonacci.vela --target linux\n");

struct Args {
    action: String,
    file: PathBuf,
    output: Option<PathBuf>,
    optimize: bool,
    timings: bool,
    options: BuildOptions,
}
fn args() -> Result<Option<Args>, String> {
    let mut iter = std::env::args().skip(1);
    let Some(action) = iter.next() else {
        print!("{HELP}");
        return Ok(None);
    };
    if action == "--help" || action == "-h" {
        print!("{HELP}");
        return Ok(None);
    }
    if action == "--version" {
        println!("vela {}", env!("CARGO_PKG_VERSION"));
        return Ok(None);
    }
    if !["check", "ir", "cfg", "asm", "build", "run"].contains(&action.as_str()) {
        return Err(format!("unknown command '{action}'; use --help"));
    }
    let mut result = Args {
        action,
        file: PathBuf::new(),
        output: None,
        optimize: false,
        timings: false,
        options: BuildOptions::host()?,
    };
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--help" | "-h" => {
                print!("{HELP}");
                return Ok(None);
            }
            "--release" => result.optimize = true,
            "--timings" => result.timings = true,
            "--no-cache" => result.options.cache = false,
            "-o" | "--output" => {
                result.output = Some(PathBuf::from(iter.next().ok_or("missing output path")?))
            }
            "--cc" => result.options.cc = iter.next().ok_or("missing assembler/linker path")?,
            "--target" => {
                result.options.target = match iter.next().as_deref() {
                    Some("windows") => Target::Windows,
                    Some("linux") => Target::Linux,
                    _ => return Err("--target requires windows or linux".into()),
                }
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option '{arg}'")),
            _ if result.file.as_os_str().is_empty() => result.file = PathBuf::from(arg),
            _ => return Err(format!("unexpected argument '{arg}'")),
        }
    }
    if result.file.as_os_str().is_empty() {
        return Err("missing .vela source file; use --help".into());
    }
    if result.file.extension().and_then(|s| s.to_str()) != Some("vela") {
        return Err("source file must have .vela extension".into());
    }
    if result.output.is_some() && ["run", "check"].contains(&result.action.as_str()) {
        return Err(format!("--output does not apply to {}", result.action));
    }
    Ok(Some(result))
}
fn protect_source(source: &Path, destination: &Path) -> Result<(), String> {
    if destination.extension().and_then(|s| s.to_str()) == Some("vela") {
        return Err("output must not use the .vela source extension".into());
    }
    if let (Ok(a), Ok(b)) = (source.canonicalize(), destination.canonicalize()) {
        if a == b {
            return Err("output would overwrite the source file".into());
        }
    }
    Ok(())
}
fn execute(args: Args) -> Result<u8, String> {
    let started = Instant::now();
    let program = vela::loader::compile_file(&args.file, args.optimize).map_err(|errors| {
        errors
            .iter()
            .map(|e| e.diagnostic.render(&e.path.to_string_lossy(), &e.source))
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    if args.timings {
        eprintln!(
            "timing frontend (load/parse/resolve/check/optimize): {:.3} ms",
            started.elapsed().as_secs_f64() * 1000.0
        );
    }
    if args.action == "ir" {
        let text = format!("{program:#?}\n");
        if let Some(output) = args.output {
            protect_source(&args.file, &output)?;
            std::fs::write(output, text).map_err(|e| e.to_string())?;
        } else {
            print!("{text}");
        }
        return Ok(0);
    }
    let started = Instant::now();
    let prepared = vela::cfg::prepare(&program, args.optimize)
        .map_err(|e| format!("{}: CFG: {e}", args.file.display()))?;
    if args.timings {
        eprintln!(
            "timing CFG verification/analysis/allocation: {:.3} ms",
            started.elapsed().as_secs_f64() * 1000.0
        );
    }
    if args.action == "check" {
        println!("OK: {}", args.file.display());
        return Ok(0);
    }
    if args.action == "cfg" {
        let text = format!("{:#?}\n", prepared.program());
        if let Some(output) = args.output {
            protect_source(&args.file, &output)?;
            std::fs::write(output, text).map_err(|e| e.to_string())?;
        } else {
            print!("{text}");
        }
        return Ok(0);
    }
    let started = Instant::now();
    let assembly = vela::cfg_codegen::emit(&prepared, args.options.target);
    if args.timings {
        eprintln!(
            "timing codegen: {:.3} ms",
            started.elapsed().as_secs_f64() * 1000.0
        );
    }
    if args.action == "asm" {
        if let Some(output) = args.output {
            protect_source(&args.file, &output)?;
            std::fs::write(output, assembly).map_err(|e| e.to_string())?;
        } else {
            print!("{assembly}");
        }
        return Ok(0);
    }
    if args.action == "run" {
        if args.options.target != Target::host()? {
            return Err("run requires the host target; use build for cross compilation".into());
        }
        let temp = Scratch::new()?;
        let binary = temp.path.join(driver::executable_name(args.options.target));
        let started = Instant::now();
        let outcome = driver::build_assembly(&assembly, &binary, &args.options)?;
        if args.timings {
            eprintln!(
                "timing native driver (cached={}): {:.3} ms",
                outcome.cached,
                started.elapsed().as_secs_f64() * 1000.0
            );
        }
        let status = Command::new(binary)
            .status()
            .map_err(|e| format!("cannot run native executable: {e}"))?;
        return Ok(status.code().map(|c| c as u8).unwrap_or(1));
    }
    let output = args.output.unwrap_or_else(|| {
        args.file
            .with_extension(if args.options.target == Target::Windows {
                "exe"
            } else {
                ""
            })
    });
    protect_source(&args.file, &output)?;
    let started = Instant::now();
    let outcome = driver::build_assembly(&assembly, &output, &args.options)?;
    if args.timings {
        eprintln!(
            "timing native driver (cached={}): {:.3} ms",
            outcome.cached,
            started.elapsed().as_secs_f64() * 1000.0
        );
    }
    println!(
        "Built {}{}",
        output.display(),
        if outcome.cached { " (cached)" } else { "" }
    );
    Ok(0)
}
fn main() -> ExitCode {
    let result = args().and_then(|args| match args {
        Some(args) => execute(args),
        None => Ok(0),
    });
    match result {
        Ok(code) => ExitCode::from(code),
        Err(message) => {
            eprintln!("vela: {message}");
            ExitCode::FAILURE
        }
    }
}
