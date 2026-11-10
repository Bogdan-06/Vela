//! Bounded local file modules with explicit aliases and source-aware diagnostics.
use crate::lexer::{self, TokenKind};
use crate::model::*;
use std::collections::{HashMap, HashSet};
use std::path::{Component, Path, PathBuf};

pub const MAX_MODULES: usize = 128;
pub const MAX_IMPORT_DEPTH: usize = 64;
pub const MAX_SOURCE_BYTES: u64 = 8 * 1024 * 1024;

#[derive(Clone, Debug)]
pub struct SourceDiagnostic {
    pub path: PathBuf,
    pub source: String,
    pub diagnostic: Diagnostic,
}

impl SourceDiagnostic {
    pub fn render(&self) -> String {
        self.diagnostic
            .render(&self.path.display().to_string(), &self.source)
    }
}

struct Module {
    path: PathBuf,
    source: String,
    program: Program,
    imports: HashMap<String, usize>,
    offset: usize,
}

struct Loader {
    root: PathBuf,
    modules: Vec<Module>,
    ids: HashMap<PathBuf, usize>,
    active: Vec<usize>,
    source_bytes: u64,
    next_line: usize,
}

/// Compile a complete local module graph. Errors retain original paths and line
/// numbers. IR spans use internal graph-wide line coordinates.
pub fn compile_file(path: &Path, optimize: bool) -> Result<IrProgram, Vec<SourceDiagnostic>> {
    let (loader, program) = load_graph(path)?;
    let ir = crate::sema::check(program).map_err(|errors| loader.diagnostics(errors))?;
    crate::finish_ir(ir, optimize).map_err(|errors| loader.diagnostics(errors))
}

/// Load a resolved AST for inspection. Internal names and graph-wide spans are
/// exposed here; use `compile_file` to preserve semantic diagnostic locations.
pub fn load(path: &Path) -> Result<Program, Vec<SourceDiagnostic>> {
    load_graph(path).map(|(_, program)| program)
}

fn load_graph(path: &Path) -> Result<(Loader, Program), Vec<SourceDiagnostic>> {
    let entry = std::fs::canonicalize(path).map_err(|error| {
        vec![standalone(
            path,
            format!("cannot read source file: {error}"),
        )]
    })?;
    let root = entry.parent().unwrap_or(Path::new(".")).to_path_buf();
    let mut loader = Loader {
        root,
        modules: Vec::new(),
        ids: HashMap::new(),
        active: Vec::new(),
        source_bytes: 0,
        next_line: 0,
    };
    loader.visit(entry, None)?;
    let mut errors = Vec::new();
    let exports: Vec<HashSet<String>> = loader
        .modules
        .iter()
        .map(|module| {
            module
                .program
                .functions
                .iter()
                .map(|f| f.name.clone())
                .collect()
        })
        .collect();
    let record_exports: Vec<HashSet<String>> = loader
        .modules
        .iter()
        .map(|module| {
            module
                .program
                .records
                .iter()
                .map(|r| r.name.clone())
                .collect()
        })
        .collect();
    if !exports[0].contains("main") {
        errors.push(Diagnostic::new(
            Span { line: 1, column: 1 },
            "entry point must be craft main() -> num: in the entry file",
        ));
    }
    let mut program = Program::default();
    for id in 0..loader.modules.len() {
        let offset = loader.modules[id].offset;
        let imports = loader.modules[id].imports.clone();
        let context = ResolveContext {
            module: id,
            offset,
            imports: &imports,
            functions: &exports,
            records: &record_exports,
        };
        let original = std::mem::take(&mut loader.modules[id].program);
        let mut names = HashSet::new();
        for mut function in original.functions {
            if !names.insert(function.name.clone()) {
                errors.push(Diagnostic::new(
                    shift(function.span, offset),
                    format!("duplicate function '{}'", function.name),
                ));
            }
            if imports.contains_key(&function.name) {
                errors.push(Diagnostic::new(
                    shift(function.span, offset),
                    format!("function '{}' conflicts with a module alias", function.name),
                ));
            }
            function.name = qualify(id, &function.name);
            function.span = shift(function.span, offset);
            context.typ(&mut function.returns, function.span, &mut errors);
            for param in &mut function.params {
                param.span = shift(param.span, offset);
                context.typ(&mut param.typ, param.span, &mut errors);
            }
            context.block(&mut function.body, &mut errors);
            program.functions.push(function);
        }
        for mut record in original.records {
            if !names.insert(record.name.clone()) {
                errors.push(Diagnostic::new(shift(record.span, offset), format!("duplicate declaration '{}'; records and functions share a declaration namespace", record.name)));
            }
            if imports.contains_key(&record.name) {
                errors.push(Diagnostic::new(
                    shift(record.span, offset),
                    format!("record '{}' conflicts with a module alias", record.name),
                ));
            }
            record.name = qualify_record(id, &record.name);
            record.span = shift(record.span, offset);
            for field in &mut record.fields {
                field.span = shift(field.span, offset);
                context.typ(&mut field.typ, field.span, &mut errors);
            }
            program.records.push(record);
        }
    }
    if errors.is_empty() {
        Ok((loader, program))
    } else {
        Err(loader.diagnostics(errors))
    }
}

impl Loader {
    fn visit(
        &mut self,
        path: PathBuf,
        origin: Option<(usize, Span)>,
    ) -> Result<usize, Vec<SourceDiagnostic>> {
        if let Some(&id) = self.ids.get(&path) {
            if self.active.contains(&id) {
                let mut chain: Vec<String> = self
                    .active
                    .iter()
                    .map(|&active| {
                        self.modules[active]
                            .path
                            .file_name()
                            .unwrap_or_default()
                            .to_string_lossy()
                            .into_owned()
                    })
                    .collect();
                chain.push(
                    path.file_name()
                        .unwrap_or_default()
                        .to_string_lossy()
                        .into_owned(),
                );
                return Err(vec![self.at_origin(
                    origin,
                    &path,
                    format!("import cycle: {}", chain.join(" -> ")),
                )]);
            }
            return Ok(id);
        }
        if self.modules.len() >= MAX_MODULES {
            return Err(vec![self.at_origin(
                origin,
                &path,
                format!("module count exceeds compiler limit of {MAX_MODULES}"),
            )]);
        }
        if self.active.len() >= MAX_IMPORT_DEPTH {
            return Err(vec![self.at_origin(
                origin,
                &path,
                format!("import depth exceeds compiler limit of {MAX_IMPORT_DEPTH}"),
            )]);
        }
        let metadata = std::fs::metadata(&path).map_err(|error| {
            vec![self.at_origin(origin, &path, format!("cannot inspect module: {error}"))]
        })?;
        if !metadata.is_file() {
            return Err(vec![self.at_origin(
                origin,
                &path,
                "module path must name a file".into(),
            )]);
        }
        if metadata.len() > MAX_SOURCE_BYTES.saturating_sub(self.source_bytes) {
            return Err(vec![self.at_origin(
                origin,
                &path,
                format!("module graph exceeds source limit of {MAX_SOURCE_BYTES} bytes"),
            )]);
        }
        let source = std::fs::read_to_string(&path).map_err(|error| {
            vec![self.at_origin(origin, &path, format!("cannot read UTF-8 module: {error}"))]
        })?;
        self.source_bytes += source.len() as u64;
        if self.source_bytes > MAX_SOURCE_BYTES {
            return Err(vec![self.at_origin(
                origin,
                &path,
                format!("module graph exceeds source limit of {MAX_SOURCE_BYTES} bytes"),
            )]);
        }
        let lines =
            lexer::tokenize(&source).map_err(|errors| local_diagnostics(&path, &source, errors))?;
        let mut import_specs = Vec::new();
        let mut import_lines = HashSet::new();
        let mut aliases = HashSet::new();
        for line in &lines {
            if !line.tokens[0].is("use") {
                continue;
            }
            if line.depth != 0 || line.span.column != 1 {
                return Err(local_diagnostics(
                    &path,
                    &source,
                    vec![Diagnostic::new(
                        line.span,
                        "use declarations must start at column one",
                    )],
                ));
            }
            let tokens = &line.tokens;
            let spec = if tokens.len() == 4 && tokens[2].is("as") {
                match (&tokens[1].kind, &tokens[3].kind) {
                    (TokenKind::Text(file), TokenKind::Word(alias))
                        if !crate::parser::reserved(alias) =>
                    {
                        Some((file.clone(), alias.clone()))
                    }
                    _ => None,
                }
            } else {
                None
            };
            let Some((file, alias)) = spec else {
                return Err(local_diagnostics(
                    &path,
                    &source,
                    vec![Diagnostic::new(
                        line.span,
                        "expected use \"relative/file.vela\" as alias",
                    )],
                ));
            };
            if !aliases.insert(alias.clone()) {
                return Err(local_diagnostics(
                    &path,
                    &source,
                    vec![Diagnostic::new(
                        tokens[3].span,
                        format!("duplicate module alias '{alias}'"),
                    )],
                ));
            }
            let relative = Path::new(&file);
            if file.is_empty()
                || file.contains('\\')
                || file.contains(':')
                || relative.is_absolute()
                || relative
                    .components()
                    .any(|c| matches!(c, Component::Prefix(_) | Component::RootDir))
                || relative.extension().and_then(|x| x.to_str()) != Some("vela")
            {
                return Err(local_diagnostics(
                    &path,
                    &source,
                    vec![Diagnostic::new(
                        tokens[1].span,
                        "imports require a relative .vela path using '/' separators",
                    )],
                ));
            }
            import_lines.insert(line.span.line);
            import_specs.push((file, alias, tokens[1].span));
        }
        let stripped: String = source
            .lines()
            .enumerate()
            .map(|(index, text)| {
                if import_lines.contains(&(index + 1)) {
                    "\n".to_string()
                } else {
                    format!("{text}\n")
                }
            })
            .collect();
        let only_imports = !import_specs.is_empty()
            && lines
                .iter()
                .all(|line| import_lines.contains(&line.span.line));
        let program = if only_imports {
            Program::default()
        } else {
            crate::parser::parse(&stripped)
                .map_err(|errors| local_diagnostics(&path, &source, errors))?
        };
        let id = self.modules.len();
        let offset = self.next_line;
        self.next_line += source.lines().count().max(1) + 1;
        self.modules.push(Module {
            path: path.clone(),
            source,
            program,
            imports: HashMap::new(),
            offset,
        });
        self.ids.insert(path.clone(), id);
        self.active.push(id);
        for (file, alias, span) in import_specs {
            let requested = path.parent().unwrap().join(file);
            let dependency = std::fs::canonicalize(&requested).map_err(|error| {
                vec![self.at_origin(
                    Some((id, span)),
                    &requested,
                    format!(
                        "cannot resolve imported module '{}': {error}",
                        requested.display()
                    ),
                )]
            })?;
            if !dependency.starts_with(&self.root) {
                return Err(vec![self.at_origin(
                    Some((id, span)),
                    &dependency,
                    "import escapes the entry directory tree".into(),
                )]);
            }
            let dependency_id = self.visit(dependency, Some((id, span)))?;
            self.modules[id].imports.insert(alias, dependency_id);
        }
        self.active.pop();
        Ok(id)
    }

    fn at_origin(
        &self,
        origin: Option<(usize, Span)>,
        requested: &Path,
        message: String,
    ) -> SourceDiagnostic {
        match origin {
            Some((id, span)) => SourceDiagnostic {
                path: self.modules[id].path.clone(),
                source: self.modules[id].source.clone(),
                diagnostic: Diagnostic::new(span, message),
            },
            None => standalone(requested, message),
        }
    }

    fn diagnostics(&self, errors: Vec<Diagnostic>) -> Vec<SourceDiagnostic> {
        errors
            .into_iter()
            .map(|mut diagnostic| {
                let module = self
                    .modules
                    .iter()
                    .rev()
                    .find(|module| diagnostic.span.line > module.offset)
                    .unwrap_or(&self.modules[0]);
                diagnostic.span.line = diagnostic.span.line.saturating_sub(module.offset).max(1);
                for (span, _) in &mut diagnostic.related {
                    span.line = span.line.saturating_sub(module.offset).max(1);
                }
                for (id, source) in self.modules.iter().enumerate() {
                    diagnostic.message = diagnostic.message.replace(
                        &format!("$m{id}$"),
                        &format!(
                            "{}::",
                            source
                                .path
                                .file_name()
                                .unwrap_or_default()
                                .to_string_lossy()
                        ),
                    );
                }
                SourceDiagnostic {
                    path: module.path.clone(),
                    source: module.source.clone(),
                    diagnostic,
                }
            })
            .collect()
    }
}

fn standalone(path: &Path, message: String) -> SourceDiagnostic {
    SourceDiagnostic {
        path: path.to_path_buf(),
        source: String::new(),
        diagnostic: Diagnostic::new(Span { line: 1, column: 1 }, message),
    }
}

fn local_diagnostics(path: &Path, source: &str, errors: Vec<Diagnostic>) -> Vec<SourceDiagnostic> {
    errors
        .into_iter()
        .map(|diagnostic| SourceDiagnostic {
            path: path.to_path_buf(),
            source: source.to_string(),
            diagnostic,
        })
        .collect()
}

fn qualify(module: usize, name: &str) -> String {
    if module == 0 && name == "main" {
        "main".into()
    } else {
        format!("$m{module}${name}")
    }
}

fn shift(span: Span, offset: usize) -> Span {
    Span {
        line: span.line + offset,
        column: span.column,
    }
}

fn qualify_record(module: usize, name: &str) -> String {
    format!("$m{module}${name}")
}

struct ResolveContext<'a> {
    module: usize,
    offset: usize,
    imports: &'a HashMap<String, usize>,
    functions: &'a [HashSet<String>],
    records: &'a [HashSet<String>],
}
impl ResolveContext<'_> {
    fn name(&self, name: &mut String, span: Span, record: bool, errors: &mut Vec<Diagnostic>) {
        let exports = if record { self.records } else { self.functions };
        let kind = if record { "record" } else { "function" };
        let target = if let Some((alias, member)) = name.split_once('.') {
            match self.imports.get(alias) {
                Some(&target) if exports[target].contains(member) => {
                    Some((target, member.to_owned()))
                }
                Some(_) => {
                    errors.push(Diagnostic::new(
                        span,
                        format!("module '{alias}' has no {kind} '{member}'"),
                    ));
                    None
                }
                None => {
                    errors.push(Diagnostic::new(
                        span,
                        format!("unknown module alias '{alias}'"),
                    ));
                    None
                }
            }
        } else if exports[self.module].contains(name) {
            Some((self.module, name.clone()))
        } else {
            errors.push(Diagnostic::new(
                span,
                format!("unknown {kind} '{name}' in this module"),
            ));
            None
        };
        if let Some((module, member)) = target {
            *name = if record {
                qualify_record(module, &member)
            } else {
                qualify(module, &member)
            };
        }
    }
    fn typ(&self, typ: &mut TypeSyntax, span: Span, errors: &mut Vec<Diagnostic>) {
        if let TypeSyntax::Named(name) = typ {
            self.name(name, span, true, errors);
        }
    }
    fn block(&self, body: &mut [Stmt], errors: &mut Vec<Diagnostic>) {
        for statement in body {
            statement.span = shift(statement.span, self.offset);
            match &mut statement.kind {
                StmtKind::Let { value, .. } | StmtKind::Say(value) | StmtKind::Return(value) => {
                    self.expr(value, errors)
                }
                StmtKind::Assign { place, value } => {
                    for projection in &mut place.projections {
                        match projection {
                            Projection::Field { span, .. } => *span = shift(*span, self.offset),
                            Projection::Index(index) => self.expr(index, errors),
                        }
                    }
                    self.expr(value, errors);
                }
                StmtKind::If { condition, yes, no } => {
                    self.expr(condition, errors);
                    self.block(yes, errors);
                    self.block(no, errors);
                }
                StmtKind::While { condition, body } => {
                    self.expr(condition, errors);
                    self.block(body, errors);
                }
            }
        }
    }
    fn expr(&self, expression: &mut Expr, errors: &mut Vec<Diagnostic>) {
        expression.span = shift(expression.span, self.offset);
        match &mut expression.kind {
            ExprKind::Unary(_, child)
            | ExprKind::Len(child)
            | ExprKind::Buffer(child)
            | ExprKind::BufferCopy(child)
            | ExprKind::ArrayRepeat(child, _) => self.expr(child, errors),
            ExprKind::Field { base, .. } => self.expr(base, errors),
            ExprKind::Binary(_, left, right) | ExprKind::Index(left, right) => {
                self.expr(left, errors);
                self.expr(right, errors);
            }
            ExprKind::Call(name, args) => {
                self.name(name, expression.span, false, errors);
                for arg in args {
                    self.expr(arg, errors);
                }
            }
            ExprKind::Record { name, fields } => {
                self.name(name, expression.span, true, errors);
                for field in fields {
                    field.span = shift(field.span, self.offset);
                    self.expr(&mut field.value, errors);
                }
            }
            ExprKind::Array(elements) => {
                for element in elements {
                    self.expr(element, errors);
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "vela_modules_{}_{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir_all(&path).unwrap();
            Self(path)
        }
        fn write(&self, path: &str, source: &str) -> PathBuf {
            let path = self.0.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(&path, source).unwrap();
            path
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn compiles_qualified_calls_and_preserves_local_namespace() {
        let scratch = Scratch::new();
        let main = scratch.write("main.vela", "use \"math.vela\" as math\ncraft square(x: num) -> num:\n    give x + 1\ncraft main() -> num:\n    give math.square(square(2))\n");
        scratch.write(
            "math.vela",
            "craft square(x: num) -> num:\n    give x * x\n",
        );
        let ir = compile_file(&main, true).unwrap();
        assert_eq!(ir.functions.len(), 3);
        assert_eq!(ir.functions[ir.main].name, "main");
        assert!(ir.functions.iter().any(|f| f.name == "$m1$square"));
    }
    #[test]
    fn buffer_construction_copy_and_transfer_resolve_imported_expressions() {
        let scratch = Scratch::new();
        let main = scratch.write("main.vela", "use \"buffers.vela\" as buffers\ncraft main() -> num:\n    keep first = buffers.make(buffer(buffers.size()))\n    keep second = buffer_copy(first)\n    give buffers.take(second) + len(first)\n");
        scratch.write("buffers.vela", "craft size() -> num:\n    give 2\ncraft make(input: buffer) -> buffer:\n    keep result = buffer_copy(input)\n    give result\ncraft take(input: buffer) -> num:\n    give len(input)\n");
        for optimize in [false, true] {
            let ir = compile_file(&main, optimize).unwrap();
            crate::cfg::prepare(&ir, optimize).unwrap();
            assert_eq!(ir.functions.len(), 4);
        }
    }
    #[test]
    fn diamond_dependencies_load_once() {
        let scratch = Scratch::new();
        let main = scratch.write("main.vela", "use \"a.vela\" as a\nuse \"b.vela\" as b\ncraft main() -> num:\n    give a.f() + b.f()\n");
        scratch.write(
            "a.vela",
            "use \"common.vela\" as c\ncraft f() -> num:\n    give c.value()\n",
        );
        scratch.write(
            "b.vela",
            "use \"common.vela\" as c\ncraft f() -> num:\n    give c.value()\n",
        );
        scratch.write("common.vela", "craft value() -> num:\n    give 4\n");
        assert_eq!(compile_file(&main, false).unwrap().functions.len(), 4);
    }
    #[test]
    fn cycles_include_import_trace() {
        let scratch = Scratch::new();
        let main = scratch.write(
            "main.vela",
            "use \"a.vela\" as a\ncraft main() -> num:\n    give 0\n",
        );
        scratch.write(
            "a.vela",
            "use \"main.vela\" as root\ncraft value() -> num:\n    give 1\n",
        );
        let errors = compile_file(&main, false).unwrap_err();
        assert!(errors[0]
            .diagnostic
            .message
            .contains("main.vela -> a.vela -> main.vela"));
        assert_eq!(errors[0].path.file_name().unwrap(), "a.vela");
    }
    #[test]
    fn rejects_missing_functions_aliases_and_namespace_leaks() {
        for (call, message) in [
            ("math.absent()", "has no function"),
            ("other.value()", "unknown module alias"),
            ("value()", "unknown function"),
        ] {
            let scratch = Scratch::new();
            let main = scratch.write(
                "main.vela",
                &format!("use \"math.vela\" as math\ncraft main() -> num:\n    give {call}\n"),
            );
            scratch.write("math.vela", "craft value() -> num:\n    give 1\n");
            let errors = compile_file(&main, false).unwrap_err();
            assert!(errors[0].diagnostic.message.contains(message));
            assert_eq!(errors[0].diagnostic.span.line, 3);
        }
    }
    #[test]
    fn imported_semantic_errors_retain_original_file_and_line() {
        let scratch = Scratch::new();
        let main = scratch.write(
            "main.vela",
            "use \"bad.vela\" as bad\ncraft main() -> num:\n    give 0\n",
        );
        scratch.write("bad.vela", "craft broken() -> num:\n    give true\n");
        let errors = compile_file(&main, false).unwrap_err();
        assert_eq!(errors[0].path.file_name().unwrap(), "bad.vela");
        assert_eq!(errors[0].diagnostic.span.line, 2);
        assert!(errors[0].source.contains("give true"));
    }
    #[test]
    fn imported_ownership_errors_localize_primary_and_related_locations() {
        let scratch = Scratch::new();
        let main = scratch.write(
            "main.vela",
            "use \"owners.vela\" as owners\ncraft main() -> num:\n    give 0\n",
        );
        scratch.write("owners.vela", "craft invalid() -> num:\n    keep b = buffer(1)\n    keep moved = b\n    give len(b)\n");
        let errors = compile_file(&main, false).unwrap_err();
        let diagnostic = errors
            .iter()
            .find(|error| {
                error
                    .diagnostic
                    .message
                    .contains("unavailable after a move")
            })
            .unwrap();
        assert_eq!(diagnostic.path.file_name().unwrap(), "owners.vela");
        assert_eq!(diagnostic.diagnostic.span.line, 4);
        assert_eq!(
            diagnostic.diagnostic.related[0].0,
            Span {
                line: 3,
                column: 18
            }
        );
        assert_eq!(
            diagnostic.diagnostic.related[1].0,
            Span { line: 2, column: 5 }
        );
        let rendered = diagnostic.render();
        assert!(rendered.contains("owners.vela:3:18: note: buffer moved here"));
        assert!(rendered.contains("owners.vela:2:5: note: buffer declared here"));
    }
    #[test]
    fn rejects_invalid_imports_and_alias_collisions() {
        for (header, message) in [
            ("use \"missing.vela\" as absent", "cannot resolve"),
            ("use \"math.vela\" math", "expected use"),
            ("use \"math.vela\" as num", "expected use"),
            (
                "use \"math.vela\" as math\nuse \"math.vela\" as math",
                "duplicate module alias",
            ),
            ("use \"math.vela\" as main", "conflicts with a module alias"),
            ("use \"math.txt\" as math", "relative .vela"),
        ] {
            let scratch = Scratch::new();
            let main = scratch.write(
                "main.vela",
                &format!("{header}\ncraft main() -> num:\n    give 0\n"),
            );
            scratch.write("math.vela", "craft value() -> num:\n    give 1\n");
            assert!(
                compile_file(&main, false).unwrap_err()[0]
                    .diagnostic
                    .message
                    .contains(message),
                "{header}"
            );
        }
    }
    #[test]
    fn rejects_escape_from_entry_directory_tree() {
        let scratch = Scratch::new();
        let main = scratch.write(
            "project/main.vela",
            "use \"../outside.vela\" as outside\ncraft main() -> num:\n    give 0\n",
        );
        scratch.write("outside.vela", "craft value() -> num:\n    give 1\n");
        assert!(compile_file(&main, false).unwrap_err()[0]
            .diagnostic
            .message
            .contains("escapes the entry directory tree"));
    }
    #[test]
    fn qualified_declarations_are_rejected_but_field_values_parse() {
        assert!(crate::parser::parse("craft math.value() -> num:\n    give 0\n").is_err());
        assert!(
            crate::parser::parse("craft main() -> num:\n    say value.field\n    give 0\n").is_ok()
        );
    }
    #[test]
    fn missing_entry_diagnostic_points_to_entry_file() {
        let scratch = Scratch::new();
        let main = scratch.write(
            "main.vela",
            "use \"lib.vela\" as lib\ncraft helper() -> num:\n    give 0\n",
        );
        scratch.write("lib.vela", "craft main() -> num:\n    give 0\n");
        let errors = compile_file(&main, false).unwrap_err();
        assert!(errors[0].diagnostic.message.contains("entry point"));
        assert_eq!(errors[0].path.file_name().unwrap(), "main.vela");
    }
    #[test]
    fn imported_main_cannot_supply_an_import_only_entry_point() {
        let scratch = Scratch::new();
        let main = scratch.write("main.vela", "# entry\nuse \"lib.vela\" as lib\n");
        scratch.write("lib.vela", "craft main() -> num:\n    give 0\n");
        let errors = compile_file(&main, false).unwrap_err();
        assert!(errors[0].diagnostic.message.contains("entry point"));
        assert_eq!(errors[0].path.file_name().unwrap(), "main.vela");
    }
    #[test]
    fn bounds_import_depth_module_count_and_total_source_size() {
        let scratch = Scratch::new();
        for index in 0..=MAX_IMPORT_DEPTH {
            let next = if index == MAX_IMPORT_DEPTH {
                String::new()
            } else {
                format!("use \"depth{}.vela\" as next\n", index + 1)
            };
            scratch.write(
                &format!("depth{index}.vela"),
                &format!("{next}craft main() -> num:\n    give 0\n"),
            );
        }
        assert!(
            compile_file(&scratch.0.join("depth0.vela"), false).unwrap_err()[0]
                .diagnostic
                .message
                .contains("import depth")
        );
        let mut source = String::new();
        for index in 0..MAX_MODULES {
            source.push_str(&format!("use \"count{index}.vela\" as m{index}\n"));
            scratch.write(
                &format!("count{index}.vela"),
                "craft f() -> num:\n    give 1\n",
            );
        }
        source.push_str("craft main() -> num:\n    give 0\n");
        let root = scratch.write("count_root.vela", &source);
        assert!(compile_file(&root, false).unwrap_err()[0]
            .diagnostic
            .message
            .contains("module count"));
        let huge = scratch.0.join("huge.vela");
        std::fs::File::create(&huge)
            .unwrap()
            .set_len(MAX_SOURCE_BYTES + 1)
            .unwrap();
        assert!(compile_file(&huge, false).unwrap_err()[0]
            .diagnostic
            .message
            .contains("source limit"));
    }

    #[test]
    fn resolves_module_calls_through_all_array_expression_positions() {
        let scratch = Scratch::new();
        let main = scratch.write("main.vela", "use \"values.vela\" as values\ncraft main() -> num:\n    change a = [values.value(), values.value()]\n    keep b = [values.value(); 2]\n    a[values.index()] = values.value()\n    say values.pair()[values.index()]\n    say len(values.pair())\n    give a[0] + b[0]\n");
        scratch.write("values.vela", "craft value() -> num:\n    give 7\ncraft index() -> num:\n    give 0\ncraft pair() -> [num; 2]:\n    give [1, 2]\n");
        for optimize in [false, true] {
            let ir = compile_file(&main, optimize).unwrap();
            crate::ir::verify(&ir).unwrap();
        }
        scratch.write("values.vela", "craft value() -> num:\n    give false\ncraft index() -> num:\n    give 0\ncraft pair() -> [num; 2]:\n    give [1, 2]\n");
        let errors = compile_file(&main, false).unwrap_err();
        assert_eq!(errors[0].path.file_name().unwrap(), "values.vela");
        assert_eq!(errors[0].diagnostic.span.line, 2);
    }

    #[test]
    fn resolves_record_exports_types_constructors_and_ordinary_value_fields() {
        let scratch = Scratch::new();
        let main = scratch.write("main.vela", "use \"types.vela\" as types\nrecord Container:\n    point: types.Point\ncraft identity(value: types.Point) -> types.Point:\n    give value\ncraft main() -> num:\n    change types = Container { point: types.Point { x: 7 } }\n    types.point.x = identity(types.point).x\n    give types.point.x\n");
        scratch.write("types.vela", "record Point:\n    x: num\n");
        let program = load(&main).unwrap();
        assert_eq!(program.records.len(), 2);
        assert!(
            matches!(&program.records[0].fields[0].typ, TypeSyntax::Named(name) if name == "$m1$Point")
        );
        assert!(
            matches!(&program.functions[0].params[0].typ, TypeSyntax::Named(name) if name == "$m1$Point")
        );
        assert!(
            matches!(&program.functions[0].returns, TypeSyntax::Named(name) if name == "$m1$Point")
        );
        for optimize in [false, true] {
            let ir = compile_file(&main, optimize).unwrap();
            assert_eq!(ir.records.len(), 2);
            crate::ir::verify(&ir).unwrap();
        }
    }

    #[test]
    fn record_names_are_module_private_and_do_not_resolve_function_exports() {
        for (declaration, message) in [
            (
                "craft f(p: Point) -> num:\n    give 0\n",
                "unknown record 'Point'",
            ),
            (
                "craft f(p: types.absent) -> num:\n    give 0\n",
                "has no record 'absent'",
            ),
            (
                "craft f(p: other.Point) -> num:\n    give 0\n",
                "unknown module alias 'other'",
            ),
            (
                "craft f() -> num:\n    keep p = types.func {}\n    give 0\n",
                "has no record 'func'",
            ),
        ] {
            let scratch = Scratch::new();
            let main = scratch.write(
                "main.vela",
                &format!(
                    "use \"types.vela\" as types\n{declaration}craft main() -> num:\n    give 0\n"
                ),
            );
            scratch.write(
                "types.vela",
                "record Point:\n    x: num\ncraft func() -> num:\n    give 1\n",
            );
            let errors = load(&main).unwrap_err();
            assert!(errors[0].diagnostic.message.contains(message), "{errors:?}");
            assert_eq!(errors[0].path.file_name().unwrap(), "main.vela");
        }
    }

    #[test]
    fn rejects_record_declaration_namespace_and_alias_collisions() {
        for declaration in [
            "record Point:\n    x: num\nrecord Point:\n    y: num\n",
            "record Point:\n    x: num\ncraft Point() -> num:\n    give 0\n",
            "record types:\n    x: num\n",
        ] {
            let scratch = Scratch::new();
            let main = scratch.write(
                "main.vela",
                &format!(
                    "use \"types.vela\" as types\n{declaration}craft main() -> num:\n    give 0\n"
                ),
            );
            scratch.write("types.vela", "record Point:\n    x: num\n");
            let errors = load(&main).unwrap_err();
            assert!(
                errors
                    .iter()
                    .any(|error| error.diagnostic.message.contains("duplicate")
                        || error
                            .diagnostic
                            .message
                            .contains("conflicts with a module alias")),
                "{errors:?}"
            );
        }
    }

    #[test]
    fn shifts_record_field_constructor_and_place_diagnostic_spans_once() {
        let scratch = Scratch::new();
        let main = scratch.write(
            "main.vela",
            "use \"values.vela\" as values\ncraft main() -> num:\n    give values.run()\n",
        );
        scratch.write("values.vela", "record Box:\n    items: [num; 2]\ncraft run() -> num:\n    change box = Box { items: [1, 2] }\n    box.items[missing()] = 3\n    give box.items[0]\n");
        let errors = compile_file(&main, false).unwrap_err();
        assert_eq!(errors[0].path.file_name().unwrap(), "values.vela");
        assert_eq!(errors[0].diagnostic.span.line, 5);
        assert!(errors[0]
            .diagnostic
            .message
            .contains("unknown function 'missing'"));
        scratch.write("values.vela", "record Box:\n    items: [num; 2]\ncraft run() -> num:\n    change box = Box { items: [1, 2] }\n    box.absent = 3\n    give 0\n");
        let errors = compile_file(&main, false).unwrap_err();
        assert_eq!(errors[0].path.file_name().unwrap(), "values.vela");
        assert_eq!(errors[0].diagnostic.span.line, 5);
        assert_eq!(errors[0].diagnostic.span.column, 9);
        assert!(!errors[0].diagnostic.message.contains("$m"));
    }
}
