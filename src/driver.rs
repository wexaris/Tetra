use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use inkwell::context::Context;
use crate::ast::{Package, PackageDef};
use crate::validate::{Crawler, ExprValidator};
use crate::cli_args::CliArgs;
use crate::codegen::Generator;
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

        let ctx = driver.generate(&package, defs.clone())?;

        Ok(())
    }

    pub fn parse(&self) -> Result<(Package, Rc<RefCell<ScopeTree>>)> {
        let mut error_count = 0usize;

        let name = self.args.name.as_ref().unwrap().clone();
        let definitions = Rc::new(RefCell::new(ScopeTree::new(name.clone())));

        let file = SourceFile::from(self.args.input.clone());
        let mut tokenizer = Tokenizer::new(file)?;
        let tokens = tokenizer.parse();

        if tokenizer.has_errors() {
            error_count += tokenizer.error_count();
            return Err(Error::StageError(error_count));
        }

        let mut parser = Parser::new(tokens, definitions.clone());
        let module = parser.parse_module();

        if parser.has_errors() {
            error_count += parser.error_count();
            return Err(Error::StageError(error_count));
        }

        let def = PackageDef::new(name);
        let package = Package {
            def,
            modules: HashMap::from([(module.def.path.clone(), module)])
        };

        if self.args.print_ast {
            display_tree::print_tree!(package);
        }

        Ok((package, definitions))
    }

    fn validate(&self, package: &mut Package, defs: Rc<RefCell<ScopeTree>>) -> Result<()> {
        let mut validator = Crawler::new(defs.clone())
            .with(Box::new(ExprValidator::new()));

        validator.visit_package(package);

        if validator.error_count() != 0 {
            return Err(Error::StageError(validator.error_count()));
        }

        Ok(())
    }

    fn generate(&self, package: &Package, defs: Rc<RefCell<ScopeTree>>) -> Result<Context> {
        let cwd = std::env::current_dir().expect("working directory inaccessible!");
        //let obj_dir = cwd.join("out");

        let mut error_count = 0usize;

        let ctx = Generator::create_context();

        for (_, module) in &package.modules {
            let gen = Generator::compile_module(&module, &ctx, defs.clone());

            if gen.has_errors() {
                error_count += gen.error_count();
                continue;
            }

            gen.write_obj_to_dir(&cwd);

            if self.args.print_ir {
                let module = gen.get_module().print_to_stderr();
            }
        }

        if error_count != 0 {
            return Err(Error::StageError(error_count));
        }

        Ok(ctx)
    }
}
