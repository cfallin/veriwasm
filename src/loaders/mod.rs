mod lucet;
pub mod types;
pub mod utils;
mod wasmtime;
use crate::loaders;
use crate::runner::Config;
use core::str::FromStr;
use loaders::lucet::*;
use loaders::types::*;
use loaders::types::{VwFuncInfo, VwMetadata};
use loaders::wasmtime::*;
use yaxpeax_core::memory::repr::process::ModuleData;

// TODO: this should be static dispatch, not dynamic dispatch
// not performance critical, but static dispatch is more rusty

pub fn load_program(config: &Config) -> VwModule {
    match config.executable_type {
        ExecutableType::Lucet => load_lucet_program(config),
        ExecutableType::Wasmtime => load_wasmtime_program(config),
    }
}

pub trait Loadable {
    // fn load_program(&self, binpath: &str) -> VwModule;
    // fn load_metadata(&self, program: &ModuleData) -> VW_Metadata;
    fn is_valid_func_name(&self, name: &String) -> bool;
    fn get_func_signatures(&self, program: &ModuleData) -> VwFuncInfo;
}

impl Loadable for ExecutableType {
    // fn load_program(&self, binpath: &str) -> VwModule {
    //     match self {
    //         ExecutableType::Lucet => load_lucet_program(binpath),
    //         ExecutableType::Wasmtime => load_wasmtime_program(binpath),
    //     }
    // }

    // fn load_metadata(&self, program: &ModuleData) -> VW_Metadata {
    //     match self {
    //         ExecutableType::Lucet => load_lucet_metadata(program),
    //         ExecutableType::Wasmtime => load_wasmtime_metadata(program),
    //     }
    // }

    fn is_valid_func_name(&self, name: &String) -> bool {
        match self {
            ExecutableType::Lucet => is_valid_lucet_func_name(name),
            ExecutableType::Wasmtime => is_valid_wasmtime_func_name(name),
        }
    }

    fn get_func_signatures(&self, program: &ModuleData) -> VwFuncInfo {
        match self {
            ExecutableType::Lucet => get_lucet_func_signatures(program),
            ExecutableType::Wasmtime => get_wasmtime_func_signatures(program),
        }
    }
}

impl FromStr for ExecutableType {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match &s.to_string().to_lowercase()[..] {
            "lucet" => Ok(ExecutableType::Lucet),
            "wasmtime" => Ok(ExecutableType::Wasmtime),
            _ => Err("Unknown executable type"),
        }
    }
}
