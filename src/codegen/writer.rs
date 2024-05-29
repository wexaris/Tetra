use std::path::PathBuf;
use inkwell::module::Module;
use inkwell::OptimizationLevel;
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple};
use crate::error::{Error, Result};

pub struct LLVMWriter<'a, 'ctx> {
    module: &'a Module<'ctx>,
}

impl<'a, 'ctx> LLVMWriter<'a, 'ctx> {
    pub fn new(module: &'a Module<'ctx>) -> Self {
        Self { module }
    }

    pub fn write_ir_to_dir<P: AsRef<std::path::Path>>(&self, path: P) -> Result<PathBuf> {
        std::fs::create_dir_all(&path).unwrap();
        let filename = self.get_mod_name().to_string() + ".ll";
        let filepath = path.as_ref().join(&filename);

        self.module.print_to_file(&filepath)
            .map_err(|e| Error::CompileError(e.to_string()))?;

        Ok(filepath)
    }

    pub fn write_bc_to_dir<P: AsRef<std::path::Path>>(&self, path: P) -> Result<PathBuf> {
        std::fs::create_dir_all(&path).unwrap();
        let filename = self.get_mod_name().to_string() + ".bc";
        let filepath = path.as_ref().join(&filename);

        if !self.module.write_bitcode_to_path(&filepath) {
            return Err(Error::CompileError("failed to write module contents".to_string()));
        }

        Ok(filepath)
    }

    pub fn write_asm_to_dir<P: AsRef<std::path::Path>>(&self, path: P) -> Result<PathBuf> {
        std::fs::create_dir_all(&path).unwrap();
        let filename = self.get_mod_name().to_string() + ".asm";
        let filepath = path.as_ref().join(&filename);

        let machine = self.setup_native_compile();
        machine.write_to_file(&self.module, FileType::Assembly, &filepath)
            .map_err(|e| Error::CompileError(e.to_string()))?;

        Ok(filepath)
    }

    pub fn write_obj_to_dir<P: AsRef<std::path::Path>>(&self, path: P) -> Result<PathBuf> {
        std::fs::create_dir_all(&path).unwrap();
        let filename = self.get_mod_name().to_string() + ".o";
        let filepath = path.as_ref().join(&filename);

        let machine = self.setup_native_compile();
        machine.write_to_file(&self.module, FileType::Object, &filepath)
            .map_err(|e| Error::CompileError(e.to_string()))?;

        Ok(filepath)
    }

    fn setup_native_compile(&self) -> TargetMachine {
        // Initialize native targets
        let config = InitializationConfig::default();
        Target::initialize_native(&config).expect("failed to initialize target!");

        // Set target triple
        let target_triple = TargetMachine::get_default_triple();
        self.module.set_triple(&target_triple);

        // Set target data layout
        let machine = self.create_target_machine(&target_triple).unwrap();
        let target_data = machine.get_target_data();
        self.module.set_data_layout(&target_data.get_data_layout());

        machine
    }

    fn create_target_machine(&self, triple: &TargetTriple) -> Option<TargetMachine> {
        let target = Target::from_triple(&triple).unwrap();

        let cpu = "generic";
        let features = "";
        let optimization = OptimizationLevel::Default;
        let reloc_mode = RelocMode::DynamicNoPic;
        let code_model = CodeModel::Default;

        target.create_target_machine(&triple, cpu, features, optimization, reloc_mode, code_model)
    }

    #[inline]
    fn get_mod_name(&self) -> &str {
        let name = self.module.get_name().to_str();
        name.expect("invalid module name!")
    }
}
