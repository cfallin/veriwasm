use crate::lattices::{ConstLattice, VariableState};
use std::ops::Range;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum HeapValue {
    /// The vmctx pointer.
    VMCtx,
    /// A value loaded from a given location.
    Load(Box<HeapValue>),
    /// An offset from a given location.
    Add(Box<HeapValue>, Box<HeapValue>),
    /// A multiplication (scaling) operation.
    Scale(Box<HeapValue>, u8),
    /// A single known constant value.
    Const(i64),
    /// A pointer to somewhere in the .text segment.
    TextPointer,
    /// A min (clamping) operation.
    Min(Box<HeapValue>, Box<HeapValue>),
}

/// A tag for a bound value. Corresponds to the field-spec index in
/// the `HeapStrategy::VMCtx`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tag(pub usize);

pub type HeapValueLattice = ConstLattice<HeapValue>;

pub type HeapLattice = VariableState<HeapValueLattice>;

impl HeapValue {
    pub fn imm(value: i64) -> Self {
        Self::Const(value)
    }

    /// Validate that expression is in "normal form":
    ///
    /// ```plain
    /// - Atom := VMCtx | Load(_) | Const(_) | TextPointer
    /// - AtomSummand := Scale(Atom, _) | Atom
    /// - AtomSum := Add(AtomSum, AtomSum) | AtomSummand
    /// - Min := Min(AtomSum, AtomSum)
    ///
    /// - Normalized := Min | AtomSum
    /// ```
    pub fn is_normalized(&self) -> bool {
        match self {
            Self::Min(a, b) => a.is_atom_sum() && b.is_atom_sum(),
            x => x.is_atom_sum(),
        }
    }

    fn is_atom_sum(&self) -> bool {
        match self {
            Self::Add(a, b) => a.is_atom_sum() && b.is_atom_sum(),
            x => x.is_atom_summand(),
        }
    }

    fn is_atom_summand(&self) -> bool {
        match self {
            Self::Scale(a, _) => a.is_atom(),
            x => x.is_atom(),
        }
    }

    fn is_atom(&self) -> bool {
        match self {
            Self::VMCtx | Self::Load(_) | Self::Const(_) | Self::TextPointer => true,
            _ => false,
        }
    }

    /// Simplify an expression to normal form.
    ///
    /// - Add distributes over Range:
    ///   - `simplify(Add(Range(a, b), c))` ->
    ///     `Range(simplify(Add(a, c)), simplify(Add(b, c)))`
    /// - Scale distributes over Range:
    ///   - `simplify(Scale(Range(a, b), k))` ->
    ///     `Range(simplify(Scale(a, k)), simplify(Scale(b, k)))`
    /// - Scale distributes over Add:
    ///   - `simplify(Scale(Add(a, b), k))` ->
    ///     `Add(simplify(Scale(a, k)), simplify(Scale(b, k)))`
    /// - `Add` and `Scale` can do constant folding with `Const`.
    /// - `Load` simplifies its inner expression as well.
    /// - Range can be flattened:
    ///   - `Range(Range(a, b), c)` -> `Range(a, c)`
    ///   - `Range(a, Range(b, c))` -> `Range(a, c)`
    ///   - `Range(Range(a, b), Range(c, d))` -> `Range(a, d)`
    /// - To avoid indefinite growth, `Load` truncates its expression
    ///   after two nested `Load`s.
    pub fn simplify(self) -> Self {
        match self {
            Self::Range(a, b) => {
                let a = a.simplify();
                let b = b.simplify();
                match (a, b) {
                    (Self::Range(a, _), Self::Range(_, b)) => Self::Range(a, b),
                    (a, Self::Range(_, b)) => Self::Range(Box::new(a), b),
                    (Self::Range(a, _), b) => Self::Range(a, Box::new(b)),
                    (a, b) => Self::Range(Box::new(a), Box::new(b)),
                }
            }
            Self::Add(a, b) => {
                let a = a.simplify();
                let b = b.simplify();
                match (a, b) {
                    // Adds distribute over Ranges if values do not
                    // wrap; if they do, or if we don't know, then the
                    // range must go to "all 64-bit values" because
                    // both i64::MIN and i64::MAX are included.
                    (Self::Range(a, b), Self::Range(c, d)) => Self::Range(
                        Box::new(Self::Add(a, c).simplify()),
                        Box::new(Self::Add(b, d).simplify()),
                    ),
                    (a, Self::Range(b, c)) => Self::Range(
                        Box::new(Self::Add(Box::new(a), b).simplify()),
                        Box::new(Self::Add(Box::new(a), c).simplify()),
                    ),
                    (Self::Range(a, b), c) => Self::Range(
                        Box::new(Self::Add(a, Box::new(c)).simplify()),
                        Box::new(Self::Add(b, Box::new(c)).simplify()),
                    ),
                    // Adds can const-prop. Wrapping is not a concern
                    // if we know the exact value.
                    (Self::Const(a), Self::Const(b)) => Self::Const(a.wrapping_add(b)),
                    (a, b) => Self::Add(Box::new(a), Box::new(b)),
                }
            }
            Self::Scale(a, k) => {
                let a = a.simplify();
                match a {
                    // Scales distribute over Ranges. TODO: wrapping?
                    Self::Range(a, b) => Self::Range(
                        Box::new(Self::Scale(a, k).simplify()),
                        Box::new(Self::Scale(b, k).simplify()),
                    ),
                    // Scales distribute over Adds (linearity!).
                    Self::Add(a, b) => Self::Add(
                        Box::new(Self::Scale(a, k).simplify()),
                        Box::new(Self::Scale(b, k).simplify()),
                    ),
                    // Scales can const-prop. Wrapping is not a
                    // concern if we know the exact value.
                    Self::Const(a) => Self::Const(a.wrapping_mul(k as i64)),
                }
            }
            Self::Load(addr) => Self::Load(Box::new(addr.simplify())),
            x => x,
        }
    }

    pub fn any64() -> Self {
        Self::Range(
            Box::new(Self::Const(i64::MIN)),
            Box::new(Self::Const(i64::MAX)),
        )
    }

    pub fn any32() -> Self {
        Self::Range(
            Box::new(Self::Const(0)),
            Box::new(Self::Const(u32::MAX as i64)),
        )
    }

    pub fn add_offset(&self, off: i64) -> Self {
        Self::Add(Box::new(self.clone()), Box::new(Self::Const(off))).simplify()
    }

    pub fn add(self, other: Self) -> Option<Self> {
        todo!()
    }

    pub fn shl(self, shift: u8) -> Option<Self> {
        todo!()
    }

    pub fn load(self) -> Option<Self> {
        todo!()
    }

    pub fn clamp32(self) -> Self {
        todo!()
    }
}
