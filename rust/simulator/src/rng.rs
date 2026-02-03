//! Deterministic RNG for simulation middleware.
//!
//! Lives in the simulator, not the VM — the VM core has no randomness.

use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use std::time::Duration;

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

    /// Sample a uniform f64 in [0, 1).
    pub fn sample_f64(&mut self) -> f64 {
        self.inner.gen::<f64>()
    }

    /// Sample a duration with symmetric relative variance around `base`.
    ///
    /// `variance` is a fraction of `base` (e.g., 0.1 gives +/-10% jitter).
    #[must_use]
    pub fn sample_duration(&mut self, base: Duration, variance: f64) -> Duration {
        if variance <= 0.0 || !variance.is_finite() {
            return base;
        }
        let base_secs = base.as_secs_f64();
        let delta = base_secs * variance;
        let jitter = (self.sample_f64() * 2.0 - 1.0) * delta;
        let secs = (base_secs + jitter).max(0.0);
        Duration::from_secs_f64(secs)
    }

    /// Return true with the given probability in [0, 1].
    pub fn should_trigger(&mut self, probability: f64) -> bool {
        if probability <= 0.0 {
            false
        } else if probability >= 1.0 {
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
        assert!(!rng.should_trigger(0.0));
        assert!(rng.should_trigger(1.0));
    }
}
