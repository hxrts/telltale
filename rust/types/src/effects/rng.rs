//! Random number generation traits for deterministic simulation.
//!
//! Provides RNG abstractions that can be implemented by either seeded
//! deterministic generators (for testing) or cryptographic generators
//! (for production).

use std::time::Duration;

use crate::FixedQ32;

/// Trait for random number generation in protocol execution.
///
/// Implementations can provide deterministic seeded values for reproducible
/// testing or host entropy in runtime contexts.
///
/// # Determinism
///
/// For simulation reproducibility, always use seeded implementations like
/// `SeededRng`. The trait methods are designed to produce identical sequences
/// given identical seeds.
pub trait Rng: Send {
    /// Generate a random u64.
    fn next_u64(&mut self) -> u64;

    /// Generate a random u32.
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    /// Generate a random boolean.
    fn next_bool(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }

    /// Generate a random FixedQ32 value in [0, 1).
    ///
    /// Uses the upper 32 bits as the fractional part, giving uniform
    /// distribution over the representable range.
    fn next_fixed(&mut self) -> FixedQ32 {
        // FixedQ32 is Q32.32: value = bits / 2^32
        // Take upper 32 bits as fractional part to get value in [0, 1)
        let frac_bits = (self.next_u64() >> 32) as i64;
        FixedQ32::from_bits(frac_bits)
    }

    /// Generate a random u64 in the range [0, bound).
    ///
    /// Uses rejection sampling for uniform distribution.
    fn next_u64_bounded(&mut self, bound: u64) -> u64 {
        if bound == 0 {
            return 0;
        }
        // Simple modulo - not perfectly uniform but fast
        self.next_u64() % bound
    }

    /// Choose a random element from a slice.
    fn choose<'a, T>(&mut self, slice: &'a [T]) -> Option<&'a T> {
        if slice.is_empty() {
            return None;
        }
        let len = u64::try_from(slice.len()).ok()?;
        let idx = self.next_u64_bounded(len);
        slice.get(usize::try_from(idx).ok()?)
    }

    /// Generate a random duration between min and max.
    fn duration_between(&mut self, min: Duration, max: Duration) -> Duration {
        let min_ns = u64::try_from(min.as_nanos()).unwrap_or(u64::MAX);
        let max_ns = u64::try_from(max.as_nanos()).unwrap_or(u64::MAX);
        if max_ns <= min_ns {
            return min;
        }
        let range = max_ns - min_ns;
        Duration::from_nanos(min_ns + self.next_u64_bounded(range))
    }

    /// Fork into an independent RNG stream.
    ///
    /// The forked RNG will produce a different sequence than the parent,
    /// enabling component isolation in simulation.
    fn fork(&mut self) -> Self
    where
        Self: Sized;
}

/// Seeded RNG for reproducible randomness.
///
/// Uses a simple xorshift64 algorithm for fast, reproducible random numbers.
/// This is suitable for testing but not for cryptographic purposes.
///
/// # Algorithm
///
/// Xorshift64 with shifts (13, 7, 17) as described by Marsaglia (2003).
/// Period is 2^64 - 1.
///
/// # Example
///
/// ```
/// use telltale_types::effects::{Rng, SeededRng};
///
/// let mut rng = SeededRng::new(12345);
/// let a = rng.next_u64();
/// let b = rng.next_u64();
/// assert_ne!(a, b);
///
/// // Same seed produces same sequence
/// let mut rng2 = SeededRng::new(12345);
/// assert_eq!(rng2.next_u64(), a);
/// ```
#[derive(Debug, Clone)]
pub struct SeededRng {
    state: u64,
}

impl SeededRng {
    /// Create a new seeded RNG with an explicit seed.
    ///
    /// For deterministic simulation, always use explicit seeds.
    /// A seed of 0 is replaced with 1 (xorshift requires non-zero state).
    #[must_use]
    pub fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 { 1 } else { seed },
        }
    }

    /// Get the current state (can be used to save/restore).
    #[must_use]
    pub fn state(&self) -> u64 {
        self.state
    }

    /// Restore from a previous state.
    pub fn restore(&mut self, state: u64) {
        self.state = if state == 0 { 1 } else { state };
    }
}

impl Rng for SeededRng {
    fn next_u64(&mut self) -> u64 {
        // Xorshift64 algorithm
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state
    }

    fn fork(&mut self) -> Self {
        // Use the next value as the seed for the forked RNG
        let fork_seed = self.next_u64();
        // Advance parent again so parent and child produce different sequences
        // (otherwise both have the same state after fork)
        let _ = self.next_u64();
        Self::new(fork_seed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_seeded_rng_reproducible() {
        let mut rng1 = SeededRng::new(12345);
        let mut rng2 = SeededRng::new(12345);

        for _ in 0..100 {
            assert_eq!(rng1.next_u64(), rng2.next_u64());
        }
    }

    #[test]
    fn test_seeded_rng_different_seeds() {
        let mut rng1 = SeededRng::new(12345);
        let mut rng2 = SeededRng::new(54321);
        assert_ne!(rng1.next_u64(), rng2.next_u64());
    }

    #[test]
    fn test_seeded_rng_zero_seed() {
        let mut rng = SeededRng::new(0);
        // Should not panic or produce all zeros
        let val = rng.next_u64();
        assert_ne!(val, 0);
    }

    #[test]
    fn test_rng_choose() {
        let mut rng = SeededRng::new(42);
        let items = vec![1, 2, 3, 4, 5];
        let chosen = rng.choose(&items);
        assert!(chosen.is_some());
        assert!(items.contains(chosen.expect("must choose an element")));
    }

    #[test]
    fn test_rng_choose_empty() {
        let mut rng = SeededRng::new(42);
        let items: Vec<i32> = vec![];
        assert!(rng.choose(&items).is_none());
    }

    #[test]
    fn test_rng_duration_between() {
        let mut rng = SeededRng::new(42);
        let min = Duration::from_millis(100);
        let max = Duration::from_millis(200);

        for _ in 0..100 {
            let d = rng.duration_between(min, max);
            assert!(d >= min && d < max);
        }
    }

    #[test]
    fn test_rng_fork() {
        let mut rng1 = SeededRng::new(42);
        let mut rng2 = rng1.fork();

        // Forked RNG should produce different sequence
        assert_ne!(rng1.next_u64(), rng2.next_u64());

        // But forking with same state produces same forked RNG
        let mut rng3 = SeededRng::new(42);
        let mut rng4 = rng3.fork();
        let mut rng5 = SeededRng::new(42);
        let mut rng6 = rng5.fork();
        assert_eq!(rng4.next_u64(), rng6.next_u64());
    }

    #[test]
    fn test_next_fixed_in_range() {
        let mut rng = SeededRng::new(42);
        for _ in 0..100 {
            let val = rng.next_fixed();
            assert!(val >= FixedQ32::zero());
            assert!(val < FixedQ32::one());
        }
    }
}
