//! Small, explicit limit types used across theory algorithms.

/// Maximum recursion iterations for bounded unfolding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuelSteps(pub u32);

impl FuelSteps {
    #[must_use]
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
}

/// Maximum communication steps before yielding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct YieldAfterSteps(pub u32);

impl YieldAfterSteps {
    #[must_use]
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
}

/// Maximum recursion unfold steps in structural algorithms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnfoldSteps(pub u32);

impl UnfoldSteps {
    #[must_use]
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
}

/// Maximum number of cached entries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CacheEntries(pub u32);

impl CacheEntries {
    #[must_use]
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
}

/// Default SISO decomposition unfold limit.
pub const DEFAULT_SISO_UNFOLD_STEPS: UnfoldSteps = UnfoldSteps(10_000);

/// Default memoized projection cache limit.
pub const DEFAULT_PROJECTOR_CACHE_ENTRIES: CacheEntries = CacheEntries(10_000);
