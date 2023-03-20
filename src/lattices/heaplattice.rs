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
    /// An unsigned min (clamping) operation.
    UMin(Box<HeapValue>, Box<HeapValue>),
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
    /// - Min := UMin(AtomSum, AtomSum)
    ///
    /// - Normalized := Min | AtomSum
    /// ```
    pub fn is_normalized(&self) -> bool {
        match self {
            Self::UMin(a, b) => a.is_atom_sum() && b.is_atom_sum(),
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
    /// - Add distributes over UMin if no wrapping (TODO: handle wrapping somehow)
    ///   - `simplify(Add(UMin(a, b), c))` ->
    ///     `UMin(simplify(Add(a, c)), simplify(Add(b, c)))`
    /// - Scale distributes over UMin:
    ///   - `simplify(Scale(UMin(a, b), k))` ->
    ///     `UMin(simplify(Scale(a, k)), simplify(Scale(b, k)))`
    /// - Scale distributes over Add:
    ///   - `simplify(Scale(Add(a, b), k))` ->
    ///     `Add(simplify(Scale(a, k)), simplify(Scale(b, k)))`
    /// - `Add` and `Scale` can do constant folding with `Const`.
    ///   - also, push constants to the right otherwise, and
    ///     reassociate constants outward.
    ///   - `Add(Const(a), Const(b))` -> `Const(a + b)`
    ///   - `Add(Const(a), b)` -> `Add(b, Const(a))`
    ///   - `Add(Add(a, Const(b)), Const(c))` -> `Add(a, Const(b + c))`
    ///   - `Add(Add(a, Const(b)), c)` -> `Add(Add(a, c), Const(b))`
    ///   - `Scale(Const(a), k)` -> `Const(a * k)`
    /// - `Load` simplifies its inner expression as well.
    /// - UMin can do some constant-folding as well, and reassociates
    ///   just as `Add` does:
    ///   - `UMin(Const(a), Const(b))` -> `Const(min(a, b))`
    ///   - `UMin(Const(a), b)` -> `UMin(b, Const(a))`
    ///   - `UMin(UMin(a, Const(b)), Const(c))` -> `UMin(a, Const(min(b, c)))`
    ///   - `UMin(UMin(a, Const(b)), c)` -> `UMin(UMin(a, c), Const(b))`
    /// - To avoid indefinite growth, `Load` truncates its expression
    ///   after two nested `Load`s.
    pub fn simplify(self) -> Self {
        fn umin(a: i64, b: i64) -> i64 {
            std::cmp::min(a as u64, b as u64) as i64
        }

        match self {
            Self::UMin(a, b) => {
                let a = a.simplify();
                let b = b.simplify();
                match (a, b) {
                    // `UMin(Const(a), Const(b))` -> `Const(min(a, b))`
                    (Self::Const(a), Self::Const(b)) => Self::Const(umin(a, b)),
                    // `UMin(Const(a), b)` -> `UMin(b, Const(a))`
                    (Self::Const(a), b) => {
                        Self::UMin(Box::new(b), Box::new(Self::Const(a))).simplify()
                    }
                    (Self::UMin(a, b), c) => {
                        let a = a.simplify();
                        let b = b.simplify();
                        match (b, c) {
                            // `UMin(UMin(a, Const(b)), Const(c))` -> `UMin(a, Const(min(b, c)))`
                            (Self::Const(b), Self::Const(c)) => {
                                Self::UMin(Box::new(a), Box::new(Self::Const(umin(b, c))))
                            }
                            // `UMin(UMin(a, Const(b)), c)` -> `UMin(UMin(a, c), Const(b))`
                            (Self::Const(b), c) => Self::UMin(
                                Box::new(Self::UMin(Box::new(a), Box::new(c))),
                                Box::new(Self::Const(b)),
                            ),
                            // `UMin(UMin(a, b), c)` -> `UMin(UMin(a, b), c)`
                            (b, c) => Self::UMin(
                                Box::new(Self::UMin(Box::new(a), Box::new(b))),
                                Box::new(c),
                            ),
                        }
                    }
                    // `UMin(a, b)` -> `UMin(a, b)`
                    (a, b) => Self::UMin(Box::new(a), Box::new(b)),
                }
            }
            Self::Add(a, b) => {
                let a = a.simplify();
                let b = b.simplify();
                match (a, b) {
                    // `Add(Const(a), Const(b))` -> `Const(a + b)`
                    (Self::Const(a), Self::Const(b)) => Self::Const(a.wrapping_add(b)),
                    // `Add(Const(a), b)` -> `Add(b, Const(a))`
                    (Self::Const(a), b) => Self::Add(Box::new(b), Box::new(Self::Const(a))),

                    // `Add(a, b)` -> `Add(a, b)`
                    (a, b) => Self::Add(Box::new(a), Box::new(b)),
                }
            }
            Self::Scale(a, k) => {
                let a = a.simplify();
                match a {
                    // TODO: have to handle wrapping -- consider:
                    // Scale(UMin(0x3fff_ffff_ffff_ffff, 0x8000_0000_0000_0000), 2) ->
                    // Scale(0x3fff_ffff_ffff_ffff, 2) -> 0x7fff_ffff_ffff_fffe
                    // UMin(0x7fff_ffff_ffff_fffe, 0) -> 0
                    // `Scale(UMin(a, b), k)` -> `UMin(Scale(a, k), Scale(b, k))`
                    Self::UMin(a, b) => Self::UMin(
                        Box::new(Self::Scale(a, k).simplify()),
                        Box::new(Self::Scale(b, k).simplify()),
                    ),
                    // `Scale(Add(a, b), k)` -> `Add(Scale(a, k), Scale(b, k))`
                    Self::Add(a, b) => Self::Add(
                        Box::new(Self::Scale(a, k).simplify()),
                        Box::new(Self::Scale(b, k).simplify()),
                    ),
                    // `Scale(Const(a), k)` -> `Const(a * k)`
                    Self::Const(a) => Self::Const(a.wrapping_mul(k as i64)),
                    a => Self::Scale(Box::new(a), k),
                }
            }
            Self::Load(addr) => Self::Load(Box::new(addr.simplify())),
            x => x,
        }
    }

    pub fn add_offset(&self, off: i64) -> Self {
        Self::Add(Box::new(self.clone()), Box::new(Self::Const(off))).simplify()
    }

    pub fn add(self, other: Self) -> Self {
        Self::Add(Box::new(self), Box::new(other)).simplify()
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
