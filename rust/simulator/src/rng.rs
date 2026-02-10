//! Deterministic RNG for simulation middleware.
//!
//! Lives in the simulator, not the VM. The VM core has no randomness.

use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::time::Duration;
use telltale_types::FixedQ32;

/// Deterministic RNG for simulation middleware.
pub struct SimRng {
    inner: ChaCha8Rng,
}

impl SimRng {
    /// Create a new RNG from a seed.
    #[must_use]
    pub fn new(seed: u64) -> Self {
        Self {
            inner: ChaCha8Rng::seed_from_u64(seed),
        }
    }

    /// Derive a child RNG from the current stream.
    ///
    /// This isolates components (e.g., network vs fault injection) so their
    /// random draws don't affect each other.
    #[must_use]
    pub fn fork(&mut self) -> Self {
        let seed = self.inner.next_u64();
        Self::new(seed)
    }

    /// Sample a uniform FixedQ32 in [0, 1).
    pub fn sample_f64(&mut self) -> FixedQ32 {
        // Generate a u32 for the fractional part, giving uniform distribution in [0, 1).
        let frac_bits = self.inner.next_u32() as i64;
        FixedQ32::from_bits(frac_bits)
    }

    /// Sample a duration with symmetric relative variance around `base`.
    ///
    /// `variance` is a fraction of `base` (e.g., 0.1 gives +/-10% jitter).
    #[must_use]
    pub fn sample_duration(&mut self, base: Duration, variance: FixedQ32) -> Duration {
        let zero = FixedQ32::zero();
        if variance <= zero || !variance.is_finite() {
            return base;
        }
        // Convert to fixed-point math
        let base_nanos = base.as_nanos() as i64;
        let base_fp = FixedQ32::try_from_i64(base_nanos).unwrap_or_else(|_| FixedQ32::zero());
        let two = FixedQ32::from_ratio(2, 1).expect("2 must be representable");
        let delta = base_fp * variance;
        let jitter = (self.sample_f64() * two - FixedQ32::one()) * delta;
        let result = (base_fp + jitter).max(zero);
        let nanos = result.to_i64_round().unwrap_or(0).max(0) as u64;
        Duration::from_nanos(nanos)
    }

    /// Return true with the given probability in [0, 1].
    pub fn should_trigger(&mut self, probability: FixedQ32) -> bool {
        let zero = FixedQ32::zero();
        let one = FixedQ32::one();
        if probability <= zero {
            false
        } else if probability >= one {
            true
        } else {
            self.sample_f64() < probability
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fork_is_deterministic() {
        let mut rng = SimRng::new(42);
        let mut child_a = rng.fork();
        let mut child_b = rng.fork();

        // Same parent seed → same sequence of fork seeds.
        let mut rng2 = SimRng::new(42);
        let mut child_a2 = rng2.fork();
        let mut child_b2 = rng2.fork();

        assert_eq!(child_a.sample_f64(), child_a2.sample_f64());
        assert_eq!(child_b.sample_f64(), child_b2.sample_f64());
    }

    #[test]
    fn test_should_trigger_bounds() {
        let mut rng = SimRng::new(7);
        assert!(!rng.should_trigger(FixedQ32::zero()));
        assert!(rng.should_trigger(FixedQ32::one()));
    }
}
