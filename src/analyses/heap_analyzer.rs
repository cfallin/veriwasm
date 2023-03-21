use crate::ir::types::Stmt;
use crate::{analyses, ir, lattices, loaders};
use analyses::{AbstractAnalyzer, AnalysisResult};
use ir::types::*;
use lattices::heaplattice::{HeapLattice, HeapValue, HeapValueLattice};
use lattices::LocIdx;
use lattices::{ConstLattice, VarState};
use loaders::types::VwMetadata;
use std::default::Default;

use ValSize::*;
use X86Regs::*;

pub struct HeapAnalyzer {
    pub metadata: VwMetadata,
}

impl AbstractAnalyzer<HeapLattice> for HeapAnalyzer {
    fn init_state(&self) -> HeapLattice {
        let mut result: HeapLattice = Default::default();
        result
            .regs
            .set_reg(Rdi, Size64, HeapValueLattice::new(HeapValue::VMCtx));
        result
    }

    fn aexec(&self, in_state: &mut HeapLattice, ir_instr: &Stmt, loc_idx: &LocIdx) -> () {
        match ir_instr {
            Stmt::Clear(dst, _srcs) => {
                if let &Value::Reg(rd, Size32) | &Value::Reg(rd, Size16) | &Value::Reg(rd, Size8) =
                    dst
                {
                    in_state
                        .regs
                        .set_reg(rd, Size64, HeapValueLattice::new(HeapValue::any32()));
                } else {
                    in_state.set_to_bot(dst)
                }
            }
            Stmt::Unop(opcode, dst, src) => self.aexec_unop(in_state, opcode, &dst, &src, loc_idx),
            Stmt::Binop(opcode, dst, src1, src2) => {
                self.aexec_binop(in_state, opcode, dst, src1, src2, loc_idx);
                in_state.adjust_stack_offset(opcode, dst, src1, src2)
            }
            Stmt::Call(_) => {
                in_state.on_call();
            }
            _ => (),
        }
    }

    fn aexec_unop(
        &self,
        in_state: &mut HeapLattice,
        opcode: &Unopcode,
        dst: &Value,
        src: &Value,
        _loc_idx: &LocIdx,
    ) -> () {
        // Any write to a 32-bit register will clear the upper 32 bits of the containing 64-bit
        // register.
        if let &Value::Reg(rd, Size32) = dst {
            in_state
                .regs
                .set_reg(rd, Size64, HeapValueLattice::new(HeapValue::any32()));
            return;
        }

        match opcode {
            Unopcode::Mov => {
                let v = self.aeval_value(in_state, src);
                in_state.set(dst, v);
            }
            Unopcode::Movsx => {
                in_state.set(dst, Default::default());
            }
            Unopcode::Lea => match src {
                Value::Mem(_, memargs) => {
                    let v = self.aeval_memargs(in_state, memargs);
                    in_state.set(dst, v);
                }
                _ => unreachable!(),
            },
        }
    }

    fn aexec_binop(
        &self,
        in_state: &mut HeapLattice,
        opcode: &Binopcode,
        dst: &Value,
        src1: &Value,
        src2: &Value,
        _loc_idx: &LocIdx,
    ) {
        match (opcode, dst) {
            (Binopcode::Add, &Value::Reg(rd, Size64)) => {
                let src1 = self.aeval_value(in_state, src1);
                let src2 = self.aeval_value(in_state, src2);
                let sum = match (src1.v, src2.v) {
                    (Some(src1), Some(src2)) => HeapValueLattice::new(src1.add(src2)),
                    _ => HeapValueLattice::default(),
                };
                in_state.regs.set_reg(rd, Size64, sum);
            }

            // Any write to a 32-bit register will clear the upper 32
            // bits of the containing 64-bit register.
            (_, &Value::Reg(rd, Size32)) => {
                in_state
                    .regs
                    .set_reg(rd, Size64, HeapValueLattice::new(HeapValue::any32()));
            }
            _ => {
                in_state.set_to_bot(dst);
            }
        }
    }
}

impl HeapAnalyzer {
    pub fn aeval_value(&self, in_state: &HeapLattice, value: &Value) -> HeapValueLattice {
        match value {
            Value::Mem(memsize, memargs) if value.is_stack_access() => {
                let offset = memargs.extract_stack_offset();
                in_state.stack.get(offset, memsize.into_bytes())
            }

            Value::Mem(memsize, memargs) => {
                let ea = self.aeval_memargs(in_state, memargs);
                ea.map(|val| val.load())
            }

            Value::Reg(regnum, size) => {
                let val = in_state.regs.get_reg(*regnum, Size64);
                if size.into_bits() <= 32 {
                    val.map(|x| x.clamp32())
                } else {
                    val
                }
            }

            Value::RIPConst => HeapValueLattice::new(HeapValue::TextPointer),

            _ => HeapValueLattice::default(),
        }
    }

    /// Evaluates to the effective address.
    pub fn aeval_memargs(&self, in_state: &HeapLattice, memargs: &MemArgs) -> HeapValueLattice {
        match memargs {
            MemArgs::Mem1Arg(arg1) => self.aeval_memarg(in_state, arg1),
            MemArgs::Mem2Args(arg1, arg2) => {
                let arg1 = self.aeval_memarg(in_state, arg1);
                let arg2 = self.aeval_memarg(in_state, arg2);
                match (arg1.v, arg2.v) {
                    (Some(arg1), Some(arg2)) => HeapValueLattice::new(arg1.add(arg2)),
                    _ => HeapValueLattice::default(),
                }
            }
            MemArgs::Mem3Args(arg1, arg2, arg3) => {
                let arg1 = self.aeval_memarg(in_state, arg1);
                let arg2 = self.aeval_memarg(in_state, arg2);
                let arg3 = self.aeval_memarg(in_state, arg3);
                match (arg1.v, arg2.v, arg3.v) {
                    (Some(arg1), Some(arg2), Some(arg3)) => {
                        HeapValueLattice::new(arg1.add(arg2).add(arg3))
                    }
                    _ => HeapValueLattice::default(),
                }
            }
            MemArgs::Mem2ArgsScale(arg1, arg2, scale) => {
                let arg1 = self.aeval_memarg(in_state, arg1);
                let arg2 = self.aeval_memarg(in_state, arg2);
                match (arg1.v, arg2.v) {
                    (Some(arg1), Some(arg2)) => HeapValueLattice::new(arg1.add(arg2.scale(*scale))),
                    _ => HeapValueLattice::default(),
                }
            }
            MemArgs::Mem3ArgsScale(arg1, arg2, arg3, scale) => {
                let arg1 = self.aeval_memarg(in_state, arg1);
                let arg2 = self.aeval_memarg(in_state, arg2);
                let arg3 = self.aeval_memarg(in_state, arg3);
                match (arg1.v, arg2.v, arg3.v) {
                    (Some(arg1), Some(arg2), Some(arg3)) => {
                        HeapValueLattice::new(arg1.add(arg2).add(arg3.scale(*scale)))
                    }
                    _ => HeapValueLattice::default(),
                }
            }
        }
    }

    pub fn aeval_memarg(&self, in_state: &HeapLattice, memarg: &MemArg) -> HeapValueLattice {
        match memarg {
            MemArg::Reg(reg, size) => in_state.regs.get_reg(*reg, *size),
            MemArg::Imm(_, _, imm) => HeapValueLattice::new(HeapValue::Const(*imm)),
        }
    }
}
