use crate::analyses::{AbstractAnalyzer, AnalysisResult, HeapAnalyzer};
use crate::checkers::Checker;
use crate::ir::types::*;
use crate::lattices::heaplattice::{HeapLattice, HeapValue, HeapValueLattice, VMCtxFieldExprs};
use crate::lattices::LocIdx;
use crate::VMCtxField;
use crate::ValidationError;
use std::collections::HashMap;

use HeapValue::*;
use ValSize::*;
use X86Regs::*;

pub struct HeapChecker<'a> {
    irmap: &'a IRMap,
    analyzer: &'a HeapAnalyzer,
    name_addr_map: &'a HashMap<u64, String>,
    vmctx_size: usize,
    fields: &'a [VMCtxField],
    base_bounds: VMCtxFieldExprs,
}

pub fn check_heap(
    result: AnalysisResult<HeapLattice>,
    irmap: &IRMap,
    analyzer: &HeapAnalyzer,
    name_addr_map: &HashMap<u64, String>,
    vmctx_size: usize,
    fields: &[VMCtxField],
) -> Result<(), ValidationError> {
    let base_bounds = VMCtxFieldExprs::new(fields);
    HeapChecker {
        irmap,
        analyzer,
        name_addr_map,
        vmctx_size,
        fields,
        base_bounds,
    }
    .check(result)
}

fn memarg_is_frame(memarg: &MemArg) -> bool {
    if let MemArg::Reg(Rbp, size) = memarg {
        assert_eq!(*size, Size64);
        true
    } else {
        false
    }
}

fn is_frame_access(v: &Value) -> bool {
    if let Value::Mem(_, memargs) = v {
        // Accept only operands of the form `[rbp + OFFSET]` where `OFFSET` is an integer. In
        // Cranelift-generated code from Wasm, there are never arrays or variable-length data in
        // the function frame, so there should never be a computed address (e.g., `[rbp + 4*eax +
        // OFFSET]`).
        match memargs {
            MemArgs::Mem1Arg(memarg) => memarg_is_frame(memarg),
            MemArgs::Mem2Args(memarg1, memarg2) => {
                memarg_is_frame(memarg1) && matches!(memarg2, MemArg::Imm(..))
            }
            _ => false,
        }
    } else {
        false
    }
}

impl Checker<HeapLattice> for HeapChecker<'_> {
    fn check(&self, result: AnalysisResult<HeapLattice>) -> Result<(), ValidationError> {
        self.check_state_at_statements(result)
    }

    fn irmap(&self) -> &IRMap {
        self.irmap
    }
    fn aexec(&self, state: &mut HeapLattice, ir_stmt: &Stmt, loc: &LocIdx) {
        self.analyzer.aexec(state, ir_stmt, loc)
    }

    fn check_pre_statement(
        &self,
        state: &HeapLattice,
        ir_stmt: &Stmt,
        loc_idx: &LocIdx,
    ) -> Result<(), ValidationError> {
        match ir_stmt {
            // Check stores and loads.
            Stmt::Unop(_, dst @ Value::Mem(sz, mem), _)
            | Stmt::Binop(_, dst @ Value::Mem(sz, mem), _, _)
            | Stmt::Clear(dst @ Value::Mem(sz, mem), _) => {
                if !dst.is_stack_access() && !dst.is_frame_access() {
                    let value = self.analyzer.aeval_memargs(state, mem);
                    self.check_heap_access(*sz, value, loc_idx)?;
                }
            }
            Stmt::Unop(_, _, src @ Value::Mem(sz, mem))
            | Stmt::Binop(_, _, src @ Value::Mem(sz, mem), _)
            | Stmt::Binop(_, _, _, src @ Value::Mem(sz, mem)) => {
                if !src.is_stack_access() && !src.is_frame_access() {
                    let value = self.analyzer.aeval_memargs(state, mem);
                    self.check_heap_access(*sz, value, loc_idx)?;
                }
            }
            _ => (),
        }
        Ok(())
    }
}

impl HeapChecker<'_> {
    fn check_heap_access(
        &self,
        sz: ValSize,
        addr: HeapValueLattice,
        loc_idx: &LocIdx,
    ) -> Result<(), ValidationError> {
        let addr = match addr.v {
            Some(addr) => addr,
            None => return Err(ValidationError::HeapUnsafe),
        };
        for (base, bound) in &self.base_bounds.base_bound {
            if addr.addr_ok(base, bound, sz.into_bytes() as usize) {
                return Ok(());
            }
        }
        Err(ValidationError::HeapUnsafe)
    }
}
