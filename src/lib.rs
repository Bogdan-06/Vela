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
