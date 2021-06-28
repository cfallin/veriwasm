mod lucet;
pub mod utils;
mod wasmtime;
pub mod types;
use crate::loaders;
use core::str::FromStr;
use loaders::lucet::*;
use loaders::types::{VwMetadata, VwFuncInfo};
use loaders::wasmtime::*;
use yaxpeax_core::memory::repr::process::ModuleData;
use loaders::types::*;



// TODO: this should be static dispatch, not dynamic dispatch
// not performance critical, but static dispatch is more rusty

pub trait Loadable {
    fn load_program(&self, binpath: &str) -> VwModule;
    // fn load_metadata(&self, program: &ModuleData) -> VW_Metadata;
    fn is_valid_func_name(&self, name: &String) -> bool;
    fn get_func_signatures(&self, program: &ModuleData) -> VwFuncInfo;
}

impl Loadable for ExecutableType {
    fn load_program(&self, binpath: &str) -> VwModule {
        match self {
            ExecutableType::Lucet => load_lucet_program(binpath),
            ExecutableType::Wasmtime => load_wasmtime_program(binpath),
        }
    }

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
