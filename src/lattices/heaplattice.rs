use crate::lattices::{ConstLattice, VariableState};
use std::ops::Range;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum HeapValue {
    /// The vmctx pointer, plus some fixed offset.
    VMCtx(u64),
    /// A value loaded out of `vmctx` at the given offset, plus some
    /// fixed offset. (In other words, `*(vmctx + self.0) + self.1`.)
    VMCtxField(u64, u64),
    /// A bound, with a tag.
    Bound(Tag),
    /// A value within a known static range. Value given is exclusive
    /// (actual value must be strictly less).
    StaticBoundedVal(Range<u64>),
    /// A value in range 0..(bound[tag] - off).
    DynamicBoundedVal(Tag, u64),
    /// A pointer to a memory area that is legal to access with offset
    /// in the given range.
    StaticBoundedMem(Range<u64>),
    /// A pointer to a memory area that is legal to access up to a
    /// dynamically-determined bound, minus the given offset. (I.e.,
    /// if the pointer is incremented, this offset increments as well,
    /// to subtract from the allowed bound.)
    DynamicBoundedMem(Tag, u64),
    /// A pointer to a RIP-relative constant value.
    RIPConst,
}

/// A tag for a bound value. Corresponds to the field-spec index in
/// the `HeapStrategy::VMCtx`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tag(pub usize);

pub type HeapValueLattice = ConstLattice<HeapValue>;

pub type HeapLattice = VariableState<HeapValueLattice>;

impl HeapValue {
    pub fn add_offset(self, off: u64) -> Option<Self> {
        match self {
            Self::VMCtx(orig_off) => Some(Self::VMCtx(orig_off.wrapping_add(off))),
            Self::VMCtxField(field_off, orig_off) => {
                Some(Self::VMCtxField(field_off, orig_off.wrapping_add(off)))
            }
            Self::Bound(tag) => None,
            Self::StaticBoundedVal(bound) if bound >= off => {
                Some(Self::StaticBoundedVal(bound - off))
            }
            Self::StaticBoundedVal(_) => None,
            Self::DynamicBoundedVal(tag, tag_adj) => {
                Some(Self::DynamicBoundedVal(tag, tag_adj.wrapping_add(off)))
            }
            Self::StaticBoundedMem(bound) if bound >= off => {
                Some(Self::StaticBoundedMem(bound - off))
            }
            Self::StaticBoundedMem(_) => None,
            Self::DynamicBoundedMem(tag, tag_adj) => {
                Some(Self::DynamicBoundedMem(tag, tag_adj.wrapping_add(off)))
            }
            Self::RIPConst => None,
        }
    }

    pub fn clamp32(self) -> Self {
        match self {
            Self::StaticBoundedVal(bound) if bound <= (u32::MAX as u64) => {
                Self::StaticBoundedVal(bound)
            }
            _ => Self::StaticBoundedVal((u32::MAX as u64) + 1),
        }
    }

    pub fn ea_2reg(a: Self, b: Self, off: u64) -> Self {
        unimplemented!()
    }

    pub fn ea_3reg(a: Self, b: Self, c: Self, scale: u8, off: u64) -> Self {
        unimplemented!()
    }

    pub fn load(self) -> Self {
        unimplemented!()
    }
}
