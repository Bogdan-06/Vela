//! Vela's compilation stages. The source language never passes through C or Rust.
pub mod cfg;
pub mod cfg_codegen;
pub mod codegen;
pub mod driver;
pub mod ir;
pub mod lexer;
pub mod loader;
pub mod model;
pub mod optimize;
pub mod parser;
pub mod sema;

use model::{Diagnostic, IrProgram};

pub fn compile(source: &str, optimize: bool) -> Result<IrProgram, Vec<Diagnostic>> {
    let ast = parser::parse(source)?;
    finish_ir(sema::check(ast)?, optimize)
}

pub(crate) fn finish_ir(mut ir: IrProgram, optimize: bool) -> Result<IrProgram, Vec<Diagnostic>> {
    let verify = |program: &IrProgram| {
        ir::verify(program).map_err(|error| {
            vec![Diagnostic::new(
                model::Span { line: 1, column: 1 },
                format!("internal compiler invariant failed: {error}"),
            )]
        })
    };
    verify(&ir)?;
    if optimize {
        optimize::run(&mut ir);
        verify(&ir)?;
    }
    Ok(ir)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_program_returns_source_diagnostics() {
        let errors = compile(
            "craft main( -> num:\n    say missing\ncraft broken() num:\n    give 0\n",
            false,
        )
        .unwrap_err();

        assert_eq!(errors.len(), 2);
        assert_eq!(errors[0].span.line, 1);
        assert!(errors[0].message.contains("expected identifier"));
        assert_eq!(errors[1].span.line, 3);
    }

    #[test]
    fn type_errors_report_their_source_location() {
        let errors = compile(
            "craft main() -> num:\n    keep answer = true\n    give answer + 1\n",
            false,
        )
        .unwrap_err();

        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].span.line, 3);
        assert!(errors[0].message.contains("expects num, got flag"));
    }

    #[test]
    fn optimization_does_not_hide_invalid_programs() {
        let errors = compile("craft main() -> num:\n    give true\n", true).unwrap_err();

        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("return value expects num"));
    }
}
