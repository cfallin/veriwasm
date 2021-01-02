use crate::analyses::{run_worklist, AbstractAnalyzer, AnalysisResult};
use crate::lattices::reachingdefslattice::{singleton, LocIdx, ReachLattice};
use crate::lattices::VarState;
use crate::lifter::{Binopcode, IRMap, Stmt, Unopcode};
use crate::utils::LucetMetadata;
use yaxpeax_core::analyses::control_flow::{VW_CFG, VW_Block};

//Top level function
pub fn analyze_reaching_defs(
    cfg: &VW_CFG,
    irmap: &IRMap,
    _metadata: LucetMetadata,
) -> AnalysisResult<ReachLattice> {
    run_worklist(cfg, irmap, &ReachingDefnAnalyzer {cfg: cfg.clone(), irmap: irmap.clone()})
}

pub struct ReachingDefnAnalyzer {
    pub cfg: VW_CFG,
    pub irmap: IRMap,
}

impl ReachingDefnAnalyzer{
    //1. get enclosing block addr
    //2. get result for that block start
    //3. run reaching def up to that point
    pub fn fetch_def(&self, result: &AnalysisResult<ReachLattice>, loc_idx: &LocIdx) -> ReachLattice{
        // println!("fetch_def = {:x} {:?}", loc_idx.addr, self.cfg.blocks.contains_key(&loc_idx.addr) );
        if self.cfg.blocks.contains_key(&loc_idx.addr){
            return result.get(&loc_idx.addr).unwrap().clone();
        }
        let block_addr = self.cfg.prev_block(loc_idx.addr).unwrap().start;
        let irblock = self.irmap.get(&block_addr).unwrap();
        let mut def_state = result.get(&block_addr).unwrap().clone();
        for (addr, instruction) in irblock.iter() {
            for (idx, ir_insn) in instruction.iter().enumerate() {
                if &loc_idx.addr == addr && (loc_idx.idx as usize) == idx{
                    return def_state
                }
                self.aexec(
                    &mut def_state,
                    ir_insn,
                    &LocIdx {
                        addr: *addr,
                        idx: idx as u32,
                    },
                );
            }
        }
        unimplemented!()        
        // result.get(&block_addr).unwrap().clone()
    }
}

impl AbstractAnalyzer<ReachLattice> for ReachingDefnAnalyzer {
    fn init_state(&self) -> ReachLattice {
        let mut s: ReachLattice = Default::default();

        s.regs.rax = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 0,
        });
        s.regs.rcx = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 1,
        });
        s.regs.rdx = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 2,
        });
        s.regs.rbx = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 3,
        });
        s.regs.rbp = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 4,
        });
        s.regs.rsi = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 5,
        });
        s.regs.rdi = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 6,
        });

        s.regs.r8 = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 7,
        });
        s.regs.r9 = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 8,
        });
        s.regs.r10 = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 9,
        });
        s.regs.r11 = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 10,
        });
        s.regs.r12 = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 11,
        });
        s.regs.r13 = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 12,
        });
        s.regs.r14 = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 13,
        });
        s.regs.r15 = singleton(LocIdx {
            addr: 0xdeadbeef,
            idx: 14,
        });

        s.stack.update(
            0x8,
            singleton(LocIdx {
                addr: 0xdeadbeef,
                idx: 15,
            }),
            4,
        );
        s.stack.update(
            0x10,
            singleton(LocIdx {
                addr: 0xdeadbeef,
                idx: 16,
            }),
            4,
        );
        s.stack.update(
            0x18,
            singleton(LocIdx {
                addr: 0xdeadbeef,
                idx: 17,
            }),
            4,
        );
        s.stack.update(
            0x20,
            singleton(LocIdx {
                addr: 0xdeadbeef,
                idx: 18,
            }),
            4,
        );
        s.stack.update(
            0x28,
            singleton(LocIdx {
                addr: 0xdeadbeef,
                idx: 19,
            }),
            4,
        );

        s
    }

    fn aexec(&self, in_state: &mut ReachLattice, ir_instr: &Stmt, loc_idx: &LocIdx) -> () {
        match ir_instr {
            Stmt::Clear(dst, _) => in_state.set(dst, singleton(loc_idx.clone())),
            Stmt::Unop(Unopcode::Mov, dst, src) => {
                if let Some(v) = in_state.get(src) {
                    if v.defs.is_empty() {
                        in_state.set(dst, singleton(loc_idx.clone()));
                    } else {
                        in_state.set(dst, v);
                    }
                } else {
                    in_state.set(dst, singleton(loc_idx.clone()));
                }
                //in_state.set(dst, singleton(loc_idx.clone()))
            }
            Stmt::Binop(Binopcode::Cmp, _, _, _) => {
                //Ignore compare
            }
            Stmt::Binop(Binopcode::Test, _, _, _) => {
                //Ignore test
            }
            Stmt::Binop(opcode, dst, src1, src2) => {
                in_state.adjust_stack_offset(opcode, dst, src1, src2);
                in_state.set(dst, singleton(loc_idx.clone()))
            }
            Stmt::Call(_) =>
            //in_state.regs.clear_regs(),
            {
                in_state.regs.rax = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 0,
                });
                in_state.regs.rcx = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 1,
                });
                in_state.regs.rdx = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 2,
                });
                in_state.regs.rbx = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 3,
                });
                in_state.regs.rbp = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 4,
                });
                in_state.regs.rsi = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 5,
                });
                in_state.regs.rdi = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 6,
                });

                in_state.regs.r8 = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 7,
                });
                in_state.regs.r9 = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 8,
                });
                in_state.regs.r10 = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 9,
                });
                in_state.regs.r11 = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 10,
                });
                in_state.regs.r12 = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 11,
                });
                in_state.regs.r13 = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 12,
                });
                in_state.regs.r14 = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 13,
                });
                in_state.regs.r15 = singleton(LocIdx {
                    addr: loc_idx.addr,
                    idx: 14,
                });
            }
            _ => (),
        }
    }
}
