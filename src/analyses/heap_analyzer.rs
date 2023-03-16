use crate::ir::types::Stmt;
use crate::{analyses, ir, lattices, loaders};
use analyses::{AbstractAnalyzer, AnalysisResult};
use ir::types::*;
use lattices::heaplattice::{HeapLattice, HeapValue, HeapValueLattice};
use lattices::LocIdx;
use lattices::{ConstLattice, VarState};
use loaders::types::VwMetadata;
use std::default::Default;

use HeapValue::*;
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
            .set_reg(Rdi, Size64, HeapValueLattice::new(VMCtx(0)));
        result
    }

    fn aexec(&self, in_state: &mut HeapLattice, ir_instr: &Stmt, loc_idx: &LocIdx) -> () {
        match ir_instr {
            Stmt::Clear(dst, _srcs) => {
                if let &Value::Reg(rd, Size32) | &Value::Reg(rd, Size16) | &Value::Reg(rd, Size8) =
                    dst
                {
                    in_state.regs.set_reg(
                        rd,
                        Size64,
                        HeapValueLattice::new(StaticBoundedVal(0..(1 << 32))),
                    );
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
            in_state.regs.set_reg(
                rd,
                Size64,
                ConstLattice {
                    v: Some(StaticBoundedVal(1 << 32)),
                },
            );
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
        match opcode {
            Binopcode::Add => {
                if let (
                    &Value::Reg(rd, Size64),
                    &Value::Reg(rs1, Size64),
                    &Value::Reg(rs2, Size64),
                ) = (dst, src1, src2)
                {
                    let rs1_val = in_state.regs.get_reg(rs1, Size64).v;
                    let rs2_val = in_state.regs.get_reg(rs2, Size64).v;
                    match (rs1_val, rs2_val) {
                        (Some(HeapBase), Some(Bounded4GB)) | (Some(Bounded4GB), Some(HeapBase)) => {
                            in_state
                                .regs
                                .set_reg(rd, Size64, ConstLattice { v: Some(HeapAddr) });
                            return;
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }

        // Any write to a 32-bit register will clear the upper 32 bits of the containing 64-bit
        // register.
        if let &Value::Reg(rd, Size32) = dst {
            in_state.regs.set_reg(
                rd,
                Size64,
                ConstLattice {
                    v: Some(Bounded4GB),
                },
            );
            return;
        }

        in_state.set_to_bot(dst);
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
                todo!()
            }

            Value::Reg(regnum, size) => {
                let val = in_state.regs.get_reg(*regnum, Size64);
                if size.into_bits() <= 32 {
                    val.map(|x| x.clamp32())
                } else {
                    val
                }
            }

            Value::Imm(_, _, immval) if immval != -1 => {
                HeapValueLattice::new(HeapValue::StaticBoundedVal((*immval as u64) + 1))
            }

            Value::RIPConst => HeapValueLattice::new(RIPConst),

            _ => HeapValueLattice::default(),
        }
    }

    /// Evaluates to the effective address.
    pub fn aeval_memargs(&self, in_state: &HeapLattice, memargs: &MemArgs) -> HeapValueLattice {
        match self {
            MemArgs::Mem1Arg(arg1) => {}
            MemArgs::Mem2Args(arg1, arg2) => {}
            MemArgs::Mem3Args(arg1, arg2, arg3) => {}
            MemArgs::MemScale(arg1, arg2, scale) => {}
            // TODO: how is x86 [rax + 8*rbx + offset] handled?
        }
    }

    pub fn aeval_memarg(&self, in_state: &HeapLattice, memarg: &MemArg) -> HeapValueLattice {
        match memarg {
            MemArg::Reg(reg, size) => in_state.regs.get_reg(reg, size),
            MemArg::Imm(ImmType::Signed, ValSize::Size32, imm) => HeapValueLattice::new(
                HeapValue::StaticBoundedVal((i32::MIN as i64)..((i32::MAX as i64) + 1)),
            ),
            MemArg::Imm(ImmType::Unsigned, ValSize::Size32, imm) => {
                HeapValueLattice::new(HeapValue::StaticBoundedVal(0..((u32::MAX as i64) + 1)))
            }
            MemArg::Imm(_, ValSize::Size64, imm) => HeapValueLattice::default(),
        }
    }
}
