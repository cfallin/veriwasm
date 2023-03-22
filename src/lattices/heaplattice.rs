use crate::lattices::{ConstLattice, VariableState};
use crate::VMCtxField;
use std::fmt::Debug;
use std::ops::Range;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum HeapValue {
    /// The vmctx pointer.
    VMCtx,
    /// A value loaded from a given location.
    Load(Box<HeapValue>),
    /// An offset from a given location. Cannot wrap: we go to the
    /// lattice's Bot value if we cannot prove this when analyzing
    /// range.
    Add(Box<HeapValue>, Box<HeapValue>),
    /// A multiplication (scaling) operation. Cannot wrap: we go to
    /// the lattice's Bot value if we cannot prove this when analyzing
    /// range.
    Scale(Box<HeapValue>, u8),
    /// A single known constant value.
    Const(i64),
    /// A pointer to somewhere in the .text segment.
    TextPointer,
    /// An unsigned min (clamping) operation.
    UMin(Box<HeapValue>, Box<HeapValue>),
    /// Some unknown value. Note that this is distinguished from Bot
    /// because it is a definite, concrete value, rather than a
    /// potential conflict.
    Unknown,
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
    /// - Atom := VMCtx | Load(_) | Const(_) | TextPointer | Unknown
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
            Self::VMCtx | Self::Load(_) | Self::Const(_) | Self::TextPointer | Self::Unknown => {
                true
            }
            _ => false,
        }
    }

    /// Simplify an expression to normal form.
    ///
    /// - Add-no-wrap distributes over UMin
    ///   - `simplify(Add(UMin(a, b), c))` ->
    ///     `UMin(simplify(Add(a, c)), simplify(Add(b, c)))`
    /// - Scale-no-wrap distributes over UMin:
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
                    (Self::UMin(a, b), c) | (c, Self::UMin(a, b)) => {
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
                    (Self::Add(a, b), c) | (c, Self::Add(a, b)) => {
                        let a = a.simplify();
                        let b = b.simplify();
                        match (b, c) {
                            // `Add(Add(a, Const(b)), Const(c))` -> `Add(a, Const(min(b, c)))`
                            (Self::Const(b), Self::Const(c)) => {
                                Self::Add(Box::new(a), Box::new(Self::Const(b.wrapping_add(c))))
                            }
                            // `Add(Add(a, Const(b)), c)` -> `Add(Add(a, c), Const(b))`
                            (Self::Const(b), c) => Self::Add(
                                Box::new(Self::Add(Box::new(a), Box::new(c))),
                                Box::new(Self::Const(b)),
                            ),
                            // `Add(Add(a, b), c)` -> `Add(Add(a, b), c)`
                            (b, c) => Self::Add(
                                Box::new(Self::Add(Box::new(a), Box::new(b))),
                                Box::new(c),
                            ),
                        }
                    }
                    // `Add(UMin(a, b), c)` -> `UMin(Add(a, c), Add(b, c))`
                    (Self::UMin(a, b), c) | (c, Self::UMin(a, b)) => {
                        let a = a.simplify();
                        let b = b.simplify();
                        Self::UMin(
                            Box::new(Self::Add(Box::new(a), Box::new(c.clone())).simplify()),
                            Box::new(Self::Add(Box::new(b), Box::new(c.clone())).simplify()),
                        )
                    }

                    // `Add(a, b)` -> `Add(a, b)`
                    (a, b) => Self::Add(Box::new(a), Box::new(b)),
                }
            }
            Self::Scale(a, k) => {
                let a = a.simplify();
                match a {
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

    pub fn scale(self, scale: u8) -> Self {
        Self::Scale(Box::new(self), scale).simplify()
    }

    pub fn load(self) -> Self {
        Self::Load(Box::new(self))
    }

    /// Truncate depth of expression at a given number of loads.
    pub fn truncate(self, max_load_depth: usize) -> Self {
        if self.load_depth() <= max_load_depth {
            self
        } else {
            match self {
                Self::Load(_) if max_load_depth == 0 => Self::Unknown,
                Self::Load(addr) => Self::Load(Box::new(addr.truncate(max_load_depth - 1))),
                Self::Add(a, b) => Self::Add(
                    Box::new(a.truncate(max_load_depth)),
                    Box::new(b.truncate(max_load_depth)),
                ),
                Self::Scale(a, k) => Self::Scale(Box::new(a.truncate(max_load_depth)), k),
                Self::UMin(a, b) => Self::UMin(
                    Box::new(a.truncate(max_load_depth)),
                    Box::new(b.truncate(max_load_depth)),
                ),
                Self::Const(_) | Self::TextPointer | Self::Unknown | Self::VMCtx => unreachable!(),
            }
        }
    }

    fn load_depth(&self) -> usize {
        match self {
            Self::VMCtx | Self::TextPointer | Self::Const(_) => 0,
            Self::Scale(a, _) => a.load_depth(),
            Self::Add(a, b) | Self::UMin(a, b) => std::cmp::max(a.load_depth(), b.load_depth()),
            Self::Load(a) => a.load_depth() + 1,
            Self::Unknown => 0,
        }
    }

    pub fn clamp32(self) -> Self {
        Self::UMin(Box::new(self), Box::new(Self::Const(u32::MAX as i64)))
    }

    pub fn any32() -> Self {
        Self::UMin(
            Box::new(Self::Unknown),
            Box::new(Self::Const(u32::MAX as i64)),
        )
    }

    /// Determine a bound on a value: either a static bound, or a
    /// symbolic bound based on the given bound variable.
    pub fn find_bound<
        T: Copy + Clone + Debug,
        Base: Fn(&HeapValue) -> bool,
        Bound: Fn(&HeapValue) -> Option<T>,
    >(
        &self,
        base: &Base,
        bound: &Bound,
    ) -> Bounded<T> {
        if let Some(bound_token) = bound(self) {
            return Bounded::Dynamic {
                bound: bound_token,
                scale: 1,
                offset: 0,
                has_base: false,
                static_max: 0,
            };
        }
        if base(self) {
            return Bounded::Static {
                has_base: true,
                max: 0,
            };
        }

        match self {
            Self::VMCtx | Self::Unknown | Self::Load(_) => Bounded::None,
            Self::TextPointer => Bounded::TextPointer,
            Self::Const(val) => Bounded::Static {
                has_base: false,
                max: *val as u64,
            },
            Self::Add(a, b) => {
                let a = a.find_bound(base, bound);
                let b = b.find_bound(base, bound);
                match (a, b) {
                    (
                        Bounded::Static {
                            has_base: has_base_a,
                            max: max_a,
                        },
                        Bounded::Static {
                            has_base: has_base_b,
                            max: max_b,
                        },
                    ) => {
                        if has_base_a && has_base_b {
                            Bounded::None
                        } else {
                            if let Some(sum) = max_a.checked_add(max_b) {
                                Bounded::Static {
                                    has_base: has_base_a || has_base_b,
                                    max: sum,
                                }
                            } else {
                                Bounded::None
                            }
                        }
                    }
                    (
                        Bounded::Static {
                            has_base: has_base_a,
                            max,
                        },
                        Bounded::Dynamic {
                            has_base: has_base_b,
                            bound,
                            scale,
                            offset,
                            static_max,
                        },
                    )
                    | (
                        Bounded::Dynamic {
                            has_base: has_base_b,
                            bound,
                            scale,
                            offset,
                            static_max,
                        },
                        Bounded::Static {
                            has_base: has_base_a,
                            max,
                        },
                    ) => {
                        if has_base_a && has_base_b {
                            Bounded::None
                        } else {
                            if let Some(sum) = max.checked_add(offset) {
                                let static_max = static_max.saturating_add(max);
                                Bounded::Dynamic {
                                    has_base: has_base_a || has_base_b,
                                    bound,
                                    scale,
                                    offset: sum,
                                    static_max,
                                }
                            } else {
                                Bounded::None
                            }
                        }
                    }
                    (Bounded::Dynamic { .. }, Bounded::Dynamic { .. }) => Bounded::None,
                    (Bounded::TextPointer, _) | (_, Bounded::TextPointer) => Bounded::TextPointer,
                    (Bounded::None, _) | (_, Bounded::None) => Bounded::None,
                }
            }
            Self::Scale(a, k) => {
                let a = a.find_bound(base, bound);
                match a {
                    Bounded::TextPointer | Bounded::None => Bounded::None,
                    Bounded::Static { has_base, max } => {
                        if has_base {
                            Bounded::None
                        } else {
                            if let Some(product) = max.checked_mul(*k as u64) {
                                Bounded::Static {
                                    has_base: false,
                                    max: product,
                                }
                            } else {
                                Bounded::None
                            }
                        }
                    }
                    Bounded::Dynamic {
                        has_base,
                        bound,
                        scale,
                        offset,
                        static_max,
                    } => {
                        if has_base {
                            Bounded::None
                        } else {
                            if let (Some(scale_product), Some(offset_product)) =
                                (scale.checked_mul(*k), offset.checked_mul(*k as u64))
                            {
                                let static_max = static_max.saturating_mul(*k as u64);
                                Bounded::Dynamic {
                                    has_base: false,
                                    bound,
                                    scale: scale_product,
                                    offset: offset_product,
                                    static_max,
                                }
                            } else {
                                Bounded::None
                            }
                        }
                    }
                }
            }
            Self::UMin(a, b) => {
                let a = a.find_bound(base, bound);
                let b = b.find_bound(base, bound);
                log::trace!("find_bound: UMin ({:?}): a = {:?} b = {:?}", self, a, b);
                match (a, b) {
                    (Bounded::TextPointer, _)
                    | (_, Bounded::TextPointer)
                    | (Bounded::None, _)
                    | (_, Bounded::None) => Bounded::None,
                    (
                        Bounded::Static {
                            has_base: has_base_a,
                            max: max_a,
                        },
                        Bounded::Static {
                            has_base: has_base_b,
                            max: max_b,
                        },
                    ) => {
                        if has_base_a == has_base_b {
                            Bounded::Static {
                                has_base: has_base_a,
                                max: std::cmp::min(max_a, max_b),
                            }
                        } else {
                            Bounded::None
                        }
                    }
                    // We can take a bound on either `a` or `b` as the
                    // overall bound, with some potential loss of
                    // precision. Here we heuristically choose a
                    // dynamic bound over a static bound to propagate
                    // upward, and the first if both are dynamic.
                    (
                        Bounded::Dynamic {
                            has_base: has_base_a,
                            bound,
                            scale,
                            offset,
                            static_max,
                        },
                        other,
                    )
                    | (
                        other,
                        Bounded::Dynamic {
                            has_base: has_base_a,
                            bound,
                            scale,
                            offset,
                            static_max,
                        },
                    ) => {
                        if other.has_base() == has_base_a {
                            Bounded::Dynamic {
                                has_base: has_base_a,
                                bound,
                                scale,
                                offset,
                                static_max: std::cmp::min(static_max, other.static_max()),
                            }
                        } else {
                            Bounded::None
                        }
                    }
                }
            }
        }
    }

    /// Determine whether an access to an address described by this
    /// HeapValue is safely within the given region.
    pub fn addr_ok(&self, base: &HeapValue, bound: &HeapValue, access_size: usize) -> bool {
        // Get a bound on our access.
        let addr_bound = self.find_bound(&|val| val == base, &|val| {
            if val == bound {
                Some(())
            } else {
                None
            }
        });

        log::debug!(
            "base: {:?} bound: {:?} addr_bound: {:?}",
            base,
            bound,
            addr_bound
        );

        match (addr_bound, bound) {
            (Bounded::Static { has_base, max }, HeapValue::Const(bound))
                if has_base && max < (*bound as u64) =>
            {
                true
            }
            (
                Bounded::Dynamic {
                    has_base,
                    static_max,
                    ..
                },
                HeapValue::Const(bound),
            ) if has_base && static_max < (*bound as u64) => true,
            (
                Bounded::Dynamic {
                    has_base,
                    bound,
                    scale,
                    offset,
                    ..
                },
                _,
            ) if has_base && scale == 1 && offset == 0 => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Bounded<T: Clone + Debug> {
    Static {
        has_base: bool,
        max: u64,
    },
    Dynamic {
        has_base: bool,
        bound: T,
        scale: u8,
        offset: u64,
        static_max: u64,
    },
    TextPointer,
    None,
}
impl<T: Clone + Debug> Bounded<T> {
    fn has_base(&self) -> bool {
        match self {
            Self::Static { has_base, .. } | Self::Dynamic { has_base, .. } => *has_base,
            _ => false,
        }
    }
    fn static_max(&self) -> u64 {
        match self {
            Self::Static { max, .. } => *max,
            Self::Dynamic { static_max, .. } => *static_max,
            _ => u64::MAX,
        }
    }
}

pub struct VMCtxFieldExprs {
    pub base_bound: Vec<(HeapValue, HeapValue)>,
}

impl VMCtxFieldExprs {
    fn field_to_base_bound(ctx: HeapValue, field: &VMCtxField) -> (HeapValue, HeapValue) {
        match field {
            VMCtxField::StaticRegion {
                base_ptr_vmctx_offset,
                heap_and_guard_size,
            } => (
                HeapValue::Load(Box::new(HeapValue::Add(
                    Box::new(ctx),
                    Box::new(HeapValue::Const(*base_ptr_vmctx_offset as i64)),
                ))),
                HeapValue::Const(*heap_and_guard_size as i64),
            ),
            VMCtxField::DynamicRegion {
                base_ptr_vmctx_offset,
                len_vmctx_offset,
                element_size,
            } => {
                let len = HeapValue::Load(Box::new(HeapValue::Add(
                    Box::new(ctx.clone()),
                    Box::new(HeapValue::Const(*len_vmctx_offset as i64)),
                )));
                let len = if *element_size != 1 {
                    assert!(*element_size < 256);
                    HeapValue::Scale(Box::new(len), *element_size as u8)
                } else {
                    len
                };
                (
                    HeapValue::Load(Box::new(HeapValue::Add(
                        Box::new(ctx),
                        Box::new(HeapValue::Const(*base_ptr_vmctx_offset as i64)),
                    ))),
                    len,
                )
            }
            VMCtxField::Field { offset, len } => {
                let base = if *offset > 0 {
                    HeapValue::Add(Box::new(ctx), Box::new(HeapValue::Const(*offset as i64)))
                } else {
                    ctx
                };
                let len = HeapValue::Const(*len as i64);
                (base, len)
            }
            VMCtxField::Import {
                ptr_vmctx_offset,
                kind,
            } => {
                let ctx = HeapValue::Load(Box::new(HeapValue::Add(
                    Box::new(ctx),
                    Box::new(HeapValue::Const(*ptr_vmctx_offset as i64)),
                )));
                Self::field_to_base_bound(ctx, &*kind)
            }
        }
    }

    pub fn new(fields: &[VMCtxField], vmctx_size: usize) -> Self {
        let mut base_bound = fields
            .iter()
            .map(|field| Self::field_to_base_bound(HeapValue::VMCtx, field))
            .collect::<Vec<_>>();
        base_bound.push(Self::field_to_base_bound(
            HeapValue::VMCtx,
            &VMCtxField::Field {
                offset: 0,
                len: vmctx_size,
            },
        ));
        Self { base_bound }
    }
}
