use std::cell::RefCell;
use std::process::Stdio;
use std::rc::Rc;
use inkwell::context::Context;
use crate::ast::{Module};
use crate::validate::{Crawler, ExprDesugar, ExprValidate};
use crate::cli_args::{CliArgs, Output};
use crate::codegen::{Generator, LLVMGenerator, LLVMWriter};
use crate::error::{Error, Result};
use crate::parse::{Parser, ScopeTree, SourceFile, Tokenizer};

pub struct Driver {
    args: Rc<CliArgs>,
}

impl Driver {
    fn new(args: CliArgs) -> Self {
        Self {
            args: Rc::new(args),
        }
    }

    pub fn run(args: CliArgs) -> Result<()> {
        let driver = Self::new(args);

        let (mut package, defs) = driver.parse()?;

        driver.validate(&mut package, defs.clone())?;

        let _ = driver.generate(&package, defs.clone())?;

        Ok(())
    }

    pub fn parse(&self) -> Result<(Module, Rc<RefCell<ScopeTree>>)> {
        let definitions = Rc::new(RefCell::new(ScopeTree::new()));

        let file = SourceFile::from(self.args.input.clone());
        let mut tokenizer = Tokenizer::new(file)?;
        let tokens = tokenizer.parse();

        if tokenizer.has_errors() {
            return Err(Error::StageError(tokenizer.error_count()));
        }

        let mut parser = Parser::new(tokens, definitions.clone());
        let module = parser.parse_module();

        if parser.has_errors() {
            return Err(Error::StageError(parser.error_count()));
        }

        Ok((module, definitions))
    }

    fn validate(&self, module: &mut Module, defs: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let mut validator = Crawler::new(defs.clone())
            .with(Box::new(ExprDesugar::new()))
            .with(Box::new(ExprValidate::new()));

        validator.visit_module(module);

        if validator.has_errors() {
            return Err(Error::StageError(validator.error_count()));
        }

        if self.args.print_ast {
            display_tree::print_tree!(*module);
        }

        Ok(())
    }

    fn generate(&self, module: &Module, defs: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let ctx = Context::create();
        let gen = LLVMGenerator::compile_module(&ctx, &module, defs.clone());

        if gen.has_errors() {
            return Err(Error::StageError(gen.error_count()));
        }

        if self.args.print_ir {
            let ir_text = gen.get_module().print_to_string();
            println!("{}", ir_text.to_str().unwrap_or("invalid UTF-8 string"));
        }

        self.build_output(gen.get_module())?;
        self.link()?;

        Ok(())
    }

    pub fn build_output(&self, module: &inkwell::module::Module) -> Result<()> {
        let writer = LLVMWriter::new(module);

        match self.args.output {
            Output::Executable | Output::LibDynamic | Output::LibStatic | Output::Objects =>
                writer.write_obj_to_dir(&self.args.dir)?,
            Output::Assembly => writer.write_asm_to_dir(&self.args.dir)?,
            Output::LlvmBitCode => writer.write_bc_to_dir(&self.args.dir)?,
            Output::LlvmIr => writer.write_ir_to_dir(&self.args.dir)?,
        };

        Ok(())
    }

    pub fn link(&self) -> Result<()> {
        match self.args.output {
            Output::Executable => {
                let mut cmd = std::process::Command::new("clang");

                cmd.arg("-o");
                cmd.arg(self.args.dir.join(&self.args.name));

                let obj_file = {
                    let in_file = self.args.input.file_stem().unwrap();
                    let mut file = self.args.dir.join(in_file);
                    file.set_extension("o");
                    file
                };
                cmd.args([obj_file]);

                cmd.stdout(Stdio::piped())
                    .spawn()
                    .expect("linking failed!")
                    .wait()
                    .unwrap();

                Ok(())
            }
            Output::LibDynamic => unimplemented!("library linking not supported yet!"),
            Output::LibStatic => unimplemented!("library linking not supported yet!"),
            _ => { Ok(()) }
        }
    }
}
