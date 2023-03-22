use std::cmp::Ordering;
use std::collections::HashMap;
use std::convert::TryFrom;

use super::LocIdx;
use crate::ir::types::{ValSize, X86Regs};
use crate::lattices::{Lattice, VarSlot};

use X86Regs::*;

#[derive(Default, PartialEq, Eq, Clone, Debug)]
pub struct X86RegsLattice<T> {
    pub map: HashMap<X86Regs, VarSlot<T>>,
    pub flags_cmp: Option<(T, T)>,
}

fn hashmap_le<T: PartialOrd>(s1: &X86RegsLattice<T>, s2: &X86RegsLattice<T>) -> bool {
    for (k1, v1) in s1.map.iter() {
        if !s2.map.contains_key(k1) {
            return false;
        } else {
            if s2.map.get(k1).unwrap() < v1 {
                return false;
            } else {
            }
        }
    }
    true
}

impl<T: PartialOrd> PartialOrd for X86RegsLattice<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if hashmap_le(self, other) {
            Some(Ordering::Less)
        } else if hashmap_le(other, self) {
            Some(Ordering::Greater)
        } else if self == other {
            Some(Ordering::Equal)
        } else {
            None
        }
    }
}

impl<T: Lattice + Clone> X86RegsLattice<T> {
    pub fn get_reg(&self, index: X86Regs, _size: ValSize) -> T {
        if let Some(slot) = self.map.get(&index) {
            slot.value.clone()
        } else {
            Default::default()
        }
    }

    pub fn get_reg_index(&self, index: u8, size: ValSize) -> T {
        let reg_index = match X86Regs::try_from(index) {
            Err(err) => panic!("{}", err),
            Ok(reg) => reg,
        };
        self.get_reg(reg_index, size)
    }

    pub fn set_reg(&mut self, index: X86Regs, size: ValSize, value: T) {
        self.map.insert(
            index,
            VarSlot {
                size: size.into_bits(),
                value,
            },
        );
    }

    pub fn set_reg_index(&mut self, index: u8, size: ValSize, value: T) -> () {
        let reg_index = match X86Regs::try_from(index) {
            Err(err) => panic!("{}", err),
            Ok(reg) => reg,
        };
        self.set_reg(reg_index, size, value)
    }

    pub fn clear_regs(&mut self) -> () {
        self.map.clear()
    }

    // TODO: should this do the inverse?
    pub fn clear_caller_save_regs(&mut self) {
        // x86-64 calling convention: rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11 must be saved by
        // the caller (are clobbered by the callee), so their states become unknown after calls.
        //
        // TODO: get calling convention from program's target ABI; on Windows, rsi and rdi are
        // callee-save. The below is thus sound but conservative (and possibly
        // false-positive-producing) on Windows.
        self.map.remove(&Rax);
        self.map.remove(&Rcx);
        self.map.remove(&Rdx);
        self.map.remove(&Rsi);
        self.map.remove(&Rdi);

        self.map.remove(&R8);
        self.map.remove(&R9);
        self.map.remove(&R10);
        self.map.remove(&R11);
        self.map.remove(&Zf);
        self.map.remove(&Cf);
        self.map.remove(&Pf);
        self.map.remove(&Sf);
        self.map.remove(&Of);
    }

    pub fn show(&self) -> () {
        println!("State = ");
        println!("{:?}", self.map);
    }
}

impl<T: Lattice + Clone> Lattice for X86RegsLattice<T> {
    fn meet(&self, other: &Self, loc_idx: &LocIdx) -> Self {
        let mut newmap: HashMap<X86Regs, VarSlot<T>> = HashMap::new();
        for (var_index, v1) in self.map.iter() {
            match other.map.get(var_index) {
                Some(v2) => {
                    let new_v = v1.value.meet(&v2.value.clone(), loc_idx);
                    let newslot = VarSlot {
                        size: std::cmp::min(v1.size, v2.size),
                        value: new_v,
                    };
                    newmap.insert(*var_index, newslot);
                }
                None => (), // this means v2 = ⊥ so v1 ∧ v2 = ⊥
            }
        }
        let flags_cmp = match (self.flags_cmp.clone(), other.flags_cmp.clone()) {
            (Some(x), Some(y)) if x == y => Some(x),
            _ => None,
        };
        X86RegsLattice {
            map: newmap,
            flags_cmp,
        }
    }
}
