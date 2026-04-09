//! Cost and epsilon vocabulary for the generic search crate.

/// Search-cost operations required by the canonical search machine.
pub trait SearchCost: Copy + Ord + Send + Sync + core::fmt::Debug + 'static {
    /// Zero cost.
    #[must_use]
    fn zero() -> Self;

    /// Saturating addition over the cost domain.
    #[must_use]
    fn saturating_add(self, rhs: Self) -> Self;

    /// Stable ordering key used by canonical frontier/proposal ordering.
    #[must_use]
    fn order_key(self) -> u128;
}

impl SearchCost for u32 {
    fn zero() -> Self {
        0
    }

    fn saturating_add(self, rhs: Self) -> Self {
        self.saturating_add(rhs)
    }

    fn order_key(self) -> u128 {
        u128::from(self)
    }
}

impl SearchCost for u64 {
    fn zero() -> Self {
        0
    }

    fn saturating_add(self, rhs: Self) -> Self {
        self.saturating_add(rhs)
    }

    fn order_key(self) -> u128 {
        u128::from(self)
    }
}

/// Fixed-point epsilon with milli precision.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct EpsilonMilli(pub u32);

impl EpsilonMilli {
    const SCALE: u128 = 1_000;

    /// The exact-search epsilon `1.0`.
    #[must_use]
    pub const fn one() -> Self {
        Self(1_000)
    }

    /// Compute the weighted frontier score `g + epsilon * h` using integer math.
    #[must_use]
    pub fn weighted_f<C: SearchCost>(self, g_cost: C, heuristic: C) -> u128 {
        g_cost.order_key() * Self::SCALE + heuristic.order_key() * u128::from(self.0)
    }
}

impl Default for EpsilonMilli {
    fn default() -> Self {
        Self::one()
    }
}
