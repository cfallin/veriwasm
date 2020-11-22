use crate::lattices::reachingdefslattice::LocIdx;
use crate::lattices::stackgrowthlattice::StackGrowthLattice;
use crate::analyses::{AbstractAnalyzer};
use crate::lifter::{Stmt, Binopcode};
use crate::ir_utils::{is_rsp, get_imm_offset};

pub struct StackAnalyzer{}

impl AbstractAnalyzer<StackGrowthLattice> for StackAnalyzer {
    fn init_state(&self) -> StackGrowthLattice {
        StackGrowthLattice::new((0,4096))
    }

    fn aexec(&self, in_state : &mut StackGrowthLattice, ir_instr : &Stmt, _loc_idx : &LocIdx) -> () {
        //println!("Stack aexec: {:?} @ {:?}", ir_instr, _loc_idx);
        match ir_instr{
            Stmt::Clear(dst) => if is_rsp(dst){*in_state = Default::default()},
            Stmt::Unop(_, dst, _) => if is_rsp(dst){*in_state = Default::default()},
            Stmt::Binop(opcode, dst, src1, src2) =>  
            if is_rsp(dst) {
                if is_rsp(src1){ 
                    let offset = get_imm_offset(src2);
                    if let Some((x,probestack)) = in_state.v{
                        match opcode{
                            Binopcode::Add => {/*println!("{:?} += {:?}",x, offset);*/ *in_state = StackGrowthLattice {v : Some ((x + offset, probestack))}},
                            Binopcode::Sub => {/*println!("{:?} -= {:?}",x, offset);*/ *in_state = StackGrowthLattice {v : Some ((x - offset, probestack))}},
                            _ => panic!("Illegal RSP write")
                        }
                    }
                    else {*in_state = Default::default() }
                }
                else{ panic!("Illegal RSP write") }
            },
            Stmt::ProbeStack(new_probestack) => 
            if let Some((x,probestack)) = in_state.v{
                *in_state = StackGrowthLattice {v : Some ((x - *new_probestack as i64, *new_probestack as i64)) }
            }
            else {*in_state = Default::default() },
            _ => ()
        }
    }
}

