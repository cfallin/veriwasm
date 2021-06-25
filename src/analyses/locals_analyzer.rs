use crate::analyses::AbstractAnalyzer;
use crate::lattices::mem_to_stack_offset;
use crate::ir::types::{Value, Binopcode, Stmt, IRMap, ValSize};
use crate::lattices::reachingdefslattice::LocIdx;
use crate::lattices::localslattice::*;
use crate::lattices::{VariableState, VarState, Lattice, VarIndex};

use SlotVal::*;

pub struct LocalsAnalyzer {
    fun_type: Vec<(VarIndex, ValSize)>
}

impl LocalsAnalyzer {
    fn aeval_val(&self, state: &LocalsLattice, value: &Value) -> SlotVal {
        match value {
            Value::Mem(memsize, memargs) => {
                if let Some(offset) = mem_to_stack_offset(memargs) {
                    state.stack.get(offset, u32::from(*memsize))
                } else {
                    Init
                }
            },
            Value::Reg(_, _) => state.get(value).unwrap_or(Uninit),
            Value::Imm(_, _, _) => Init,
            Value::RIPConst => todo!(),
        }
    }

    // if all values are initialized then the value is initialized
    fn aeval_vals(&self, state: &LocalsLattice, values: &Vec<Value>) -> SlotVal {
        values.iter().fold(Init, |acc, value| -> SlotVal {
            if (acc == Init) && (self.aeval_val(state, value) == Init) {
                Init
            } else {
                Uninit
            }})
    }
}

impl AbstractAnalyzer<LocalsLattice> for LocalsAnalyzer {
    fn init_state(&self) -> LocalsLattice {
        let mut lattice: LocalsLattice = Default::default();
        for arg in self.fun_type.iter() {
            match arg {
                (VarIndex::Stack(offset), size) => {
                    lattice.stack.update(i64::from(*offset), Init, u32::from(*size))
                },
                (VarIndex::Reg(reg_num), size) => {
                    lattice.regs.set_reg(*reg_num, *size, Init)
                },
            }
        }
        lattice
    }

    fn aexec(&self, in_state: &mut LocalsLattice, ir_instr: &Stmt, loc_idx: &LocIdx) -> () {
        match ir_instr {
            Stmt::Clear(dst, srcs) => {
                in_state.set(dst, self.aeval_vals(in_state, srcs))
            }
            Stmt::Unop(_, dst, src) => {
                in_state.set(dst, self.aeval_val(in_state, src))
            }
            Stmt::Binop(_, dst, src1, src2) => {
                let dst_val = self.aeval_val(in_state, src1).meet(&self.aeval_val(in_state, src2), loc_idx);
                in_state.set(dst, dst_val)
            }
            Stmt::Call(_) => todo!(),
            _ => todo!()
        }
    }

    fn process_branch(
        &self,
        _irmap: &IRMap,
        in_state: &LocalsLattice,
        succ_addrs: &Vec<u64>,
        _addr: &u64,
    ) -> Vec<(u64, LocalsLattice)> {
        succ_addrs
            .into_iter()
            .map(|addr| (addr.clone(), in_state.clone()))
            .collect()
    }
}
