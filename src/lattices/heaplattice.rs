use crate::lattices::{ConstLattice, VariableState};
use std::ops::Range;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum HeapValue {
    /// The vmctx pointer, plus some fixed offset.
    VMCtx(i64),
    /// A value loaded out of `vmctx` at the given offset, plus some
    /// fixed offset. (In other words, `*(vmctx + self.0) + self.1`.)
    VMCtxField(i64, i64),
    /// A bound, with a tag, in units specified by the static
    /// multiplier.
    Bound(Tag, usize),
    /// A value within a known static range. Value given is exclusive
    /// (actual value must be strictly less).
    StaticBoundedVal(Range<i64>),
    /// A value in range 0..(bound[tag] - off).
    DynamicBoundedVal(Tag, i64),
    /// A pointer to a memory area that is legal to access with offset
    /// in the given range.
    StaticBoundedMem(Range<i64>),
    /// A pointer to a memory area that is legal to access up to a
    /// dynamically-determined bound, minus the given offset. (I.e.,
    /// if the pointer is incremented, this offset increments as well,
    /// to subtract from the allowed bound.)
    DynamicBoundedMem(Tag, i64),
    /// A known, constant value.
    Const(i64),
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
    pub fn imm(self, value: i64) -> Self {
        Self::Const(value)
    }

    pub fn add_offset(self, off: i64) -> Option<Self> {
        self.add(Self::Constant(off))
    }

    pub fn clamp32(self) -> Self {
        match self {
            Self::StaticBoundedVal(bound)
                if (bound.start as u32) == bound.start && (bound.end as u32) == bound.end =>
            {
                self
            }
            Self::Const(val) => Self::Const(val & (u32::MAX as i64)),
            _ => Self::StaticBoundedVal(0..(u32::MAX as u64) + 1),
        }
    }

    pub fn add(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::VMCtx(orig_off), Self::Const(off)) => {
                Some(Self::VMCtx(orig_off.wrapping_add(off)))
            }
            (Self::VMCtxField(field_off, orig_off), Self::Const(off)) => {
                Some(Self::VMCtxField(field_off, orig_off.wrapping_add(off)))
            }
            (Self::Bound(tag), Self::Const(off)) => None,
            (Self::StaticBoundedVal(range), Self::Const(off)) => Some(Self::StaticBoundedVal(
                range.start.checked_add(off)?..range.end.checked_add(off)?,
            )),
            (Self::DynamicBoundedVal(tag, tag_adj), Self::Const(off)) => {
                Some(Self::DynamicBoundedVal(tag, tag_adj.wrapping_add(off)))
            }
            (Self::StaticBoundedMem(range), Self::Const(off)) => Some(Self::StaticBoundedMem(
                range.start.checked_sub(off)?..range.end.checked_sub(off)?,
            )),
            (Self::DynamicBoundedMem(tag, tag_adj), Self::Const(off)) => {
                Some(Self::DynamicBoundedMem(tag, tag_adj.wrapping_add(off)))
            }

            (Self::StaticBoundedVal(range), Self::StaticBoundedVal(other_range)) => {
                let start = range.start.checked_add(other_range.start)?;
                let end = range.end.checked_add(other_range.end)?;
                Some(Self::StaticBoundedVal(start..end))
            }
            (Self::StaticBoundedMem(range), Self::StaticBoundedVal(other_range))
            | (Self::StaticBoundedVal(other_range), Self::StaticBoundedMem(range)) => {
                let start = range.start.checked_sub(other_range.end)?;
                let end = range.end.checked_sub(other_range.start)?;
                Some(Self::StaticBoundedMem(start..end))
            }

            (Self::DynamicBoundedMem(tag, off), Self::StaticBoundedVal(range))
            | (Self::StaticBoundedVal(range), Self::DynamicBoundedMem(tag, off)) => {
                let new_off = off.checked_sub(range.end)?;
                Self::DynamicBoundedMem(tag, new_off)
            }

            (Self::Const(val), Self::Const(off)) => Some(Self::Const(val.wrapping_add(off))),
            (other, Self::Const(_)) => other.add(self),

            (Self::RIPConst, _) => None,
            (_, Self::RIPConst) => None,
        }
    }

    pub fn shl(self, shift: usize) -> Option<Self> {
        todo!()
    }

    pub fn load(self, vmctx_fields: &[VMCtxField]) -> Option<Self> {
        match self {
            Self::VMCtx(off) => {
                for (field_idx, field) in vmctx_fields.iter().enumerate() {
                    if let Some(value) = Self::load_vmctx_at_offset(field_idx, field, off as usize)
                    {
                        return Some(value);
                    }
                }
                Some(Self::VMCtxField(off, 0))
            }
            Self::VMCtxField(field_off, off) => {
                for (field_idx, field) in vmctx_fields.iter().enumerate() {
                    if let &VMCtxField::Import {
                        ptr_vmctx_offset,
                        ref kind,
                    } = field
                    {
                        if ptr_vmctx_offset == (field_off as usize) {
                            if let Some(value) =
                                Self::load_vmctx_at_offset(field_idx, &*kind, off as usize)
                            {
                                return Some(value);
                            }
                        }
                    }
                }
            }
            _ => None,
        }
    }

    fn load_vmctx_at_offset(field_idx: usize, field: &VMCtxField, offset: usize) -> Option<Self> {
        match field {
            &VMCtxField::StaticRegion {
                base_ptr_vmctx_offset,
                heap_and_guard_size,
            } if base_ptr_vmctx_offset == (off as usize) => {
                Some(Self::StaticBoundedMem(0..(heap_and_guard_size as i64)))
            }
            &VMCtxField::DynamicRegion {
                base_ptr_vmctx_offset,
                ..
            } if base_ptr_vmctx_offset == (off as usize) => {
                let tag = Tag(field_idx);
                Some(Self::DynamicBoundedMem(tag, 0))
            }
            &VMCtxField::DynamicRegion {
                len_vmctx_offset,
                element_size,
                ..
            } if len_vmctx_offset == (off as usize) => {
                let tag = Tag(field_idx);
                Some(Self::Bound(tag, element_size))
            }
            _ => None,
        }
    }
}
