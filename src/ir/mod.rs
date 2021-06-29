mod aarch64;
mod cfg;
pub mod types;
pub mod utils;
mod x64;

pub use self::cfg::fully_resolved_cfg;
pub use self::x64::lift_cfg;
use crate::ir::types::Stmt;
use crate::loaders::types::VwArch;
use crate::VwMetadata;
use core::str::FromStr;

pub trait Liftable {
    fn lift(
        &self,
        instr: &yaxpeax_x86::long_mode::Instruction,
        addr: &u64,
        metadata: &VwMetadata,
    ) -> Vec<Stmt>;
}
// TODO: make static dispatch
impl Liftable for VwArch {
    fn lift(
        &self,
        instr: &yaxpeax_x86::long_mode::Instruction,
        addr: &u64,
        metadata: &VwMetadata,
    ) -> Vec<Stmt> {
        match self {
            VwArch::X64 => x64::lift(instr, addr, metadata),
            VwArch::Aarch64 => aarch64::lift(instr, addr, metadata),
        }
    }
}

impl FromStr for VwArch {
    type Err = &'static str;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match &s.to_string().to_lowercase()[..] {
            "x86_64" => Ok(VwArch::X64),
            "x64" => Ok(VwArch::X64),
            "aarch64" => Ok(VwArch::Aarch64),
            _ => Err("Unknown architecture"),
        }
    }
}
