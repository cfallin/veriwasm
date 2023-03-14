mod heap_analyzer;
use crate::ir::types::*;
use crate::lattices::LocIdx;
use crate::lattices::{Lattice, VarState};
use std::collections::{HashMap, VecDeque};
use yaxpeax_core::analyses::control_flow::VW_CFG;

/*     Public API     */
pub use self::heap_analyzer::HeapAnalyzer;

pub type AnalysisResult<T> = HashMap<u64, T>;

pub trait AbstractAnalyzer<State: Lattice + VarState + Clone> {
    fn init_state(&self) -> State {
        Default::default()
    }
    fn process_branch(
        &self,
        _irmap: &IRMap,
        in_state: &State,
        succ_addrs: &Vec<u64>,
        _addr: &u64,
    ) -> Vec<(u64, State)> {
        succ_addrs
            .into_iter()
            .map(|addr| (addr.clone(), in_state.clone()))
            .collect()
    }
    fn aexec_unop(
        &self,
        in_state: &mut State,
        _opcode: &Unopcode,
        dst: &Value,
        _src: &Value,
        _loc_idx: &LocIdx,
    ) -> () {
        in_state.set_to_bot(dst)
    }
    fn aexec_binop(
        &self,
        in_state: &mut State,
        opcode: &Binopcode,
        dst: &Value,
        _src1: &Value,
        _src2: &Value,
        _loc_idx: &LocIdx,
    ) -> () {
        match opcode {
            Binopcode::Cmp => (),
            Binopcode::Test => (),
            _ => in_state.set_to_bot(dst),
        }
    }

    fn aexec(&self, in_state: &mut State, ir_instr: &Stmt, loc_idx: &LocIdx) -> () {
        match ir_instr {
            Stmt::Clear(dst, _srcs) => in_state.set_to_bot(dst),
            Stmt::Unop(opcode, dst, src) => self.aexec_unop(in_state, opcode, &dst, &src, loc_idx),
            Stmt::Binop(opcode, dst, src1, src2) => {
                self.aexec_binop(in_state, opcode, dst, src1, src2, loc_idx);
                in_state.adjust_stack_offset(opcode, dst, src1, src2)
            }
            Stmt::Call(_) => in_state.on_call(),
            _ => (),
        }
    }

    fn analyze_block(&self, state: &State, irblock: &IRBlock) -> State {
        let mut new_state = state.clone();
        for (addr, instruction) in irblock.iter() {
            for (idx, ir_insn) in instruction.iter().enumerate() {
                log::debug!(
                    "Analyzing insn @ 0x{:x}: {:?}: state = {:?}",
                    addr,
                    ir_insn,
                    new_state
                );
                self.aexec(
                    &mut new_state,
                    ir_insn,
                    &LocIdx {
                        addr: *addr,
                        idx: idx as u32,
                    },
                );
            }
        }
        new_state
    }
}

fn align_succ_addrs(addr: u64, succ_addrs: Vec<u64>) -> Vec<u64> {
    if succ_addrs.len() != 2 {
        return succ_addrs;
    }
    let a1 = succ_addrs[0];
    let a2 = succ_addrs[1];
    if a1 < addr {
        return vec![a2, a1];
    }
    if a2 < addr {
        return vec![a1, a2];
    }
    if a1 < a2 {
        return vec![a1, a2];
    }
    if a1 >= a2 {
        return vec![a2, a1];
    }
    panic!("Unreachable");
}

pub fn run_worklist<T: AbstractAnalyzer<State>, State: VarState + Lattice + Clone>(
    cfg: &VW_CFG,
    irmap: &IRMap,
    analyzer: &T,
) -> AnalysisResult<State> {
    let mut statemap: HashMap<u64, State> = HashMap::new();
    let mut worklist: VecDeque<u64> = VecDeque::new();
    worklist.push_back(cfg.entrypoint);
    statemap.insert(cfg.entrypoint, analyzer.init_state());

    log::debug!(
        "Starting worklist: entry = 0x{:x} IRMap = {:?}",
        cfg.entrypoint,
        irmap
    );
    while !worklist.is_empty() {
        let addr = worklist.pop_front().unwrap();
        log::debug!("Block worklist: 0x{:x}", addr);
        let irblock = irmap.get(&addr).unwrap();
        log::debug!(" -> IR block: {:?}", irblock);
        let state = statemap.get(&addr).unwrap();
        log::debug!(" -> block state: {:?}", state);
        let new_state = analyzer.analyze_block(state, irblock);
        let succ_addrs_unaligned: Vec<u64> = cfg.graph.neighbors(addr).collect();
        let succ_addrs: Vec<u64> = align_succ_addrs(addr, succ_addrs_unaligned);
        log::debug!("Processing Block: 0x{:x} -> {:?}", addr, succ_addrs);
        for (succ_addr, branch_state) in
            analyzer.process_branch(irmap, &new_state, &succ_addrs, &addr)
        {
            let has_change = if statemap.contains_key(&succ_addr) {
                log::debug!("Processing edge from 0x{:x} to 0x{:x}", addr, succ_addr);
                let old_state = statemap.get(&succ_addr).unwrap();
                log::debug!(" -> old state: {:?}", old_state);
                log::debug!(" -> branch state: {:?}", branch_state);
                let merged_state = old_state.meet(&branch_state, &LocIdx { addr: addr, idx: 0 });

                if merged_state > *old_state {
                    log::debug!("{:?} {:?}", merged_state, old_state);
                    panic!("Meet monoticity error");
                }
                let has_change = *old_state != merged_state;
                log::debug!(
                    "At block 0x{:x}: merged input {:?}",
                    succ_addr,
                    merged_state
                );
                statemap.insert(succ_addr, merged_state);
                has_change
            } else {
                log::debug!("At block 0x{:x}: new input {:?}", succ_addr, branch_state);
                statemap.insert(succ_addr, branch_state);
                true
            };

            if has_change && !worklist.contains(&succ_addr) {
                worklist.push_back(succ_addr);
            }
        }
    }
    statemap
}
