//! Clock and RNG traits for deterministic simulation.
//!
//! This module re-exports the core effect traits from `telltale_types::effects`
//! and provides async extensions for use in choreography testing.
//!
//! # Re-exports
//!
//! The following are re-exported from `telltale_types::effects`:
//! - `Clock` - Monotonic time trait
//! - `WallClock` - Wall-clock time trait
//! - `MockClock` - Deterministic mock clock
//! - `Rng` - Random number generation trait
//! - `SeededRng` - Xorshift64-based seeded RNG
//!
//! # Async Extensions
//!
//! This module adds `AsyncClock` which extends `Clock` with async sleep.

use std::time::Duration;

// Re-export core traits and implementations from telltale-types
pub use telltale_types::effects::{Clock, MockClock, Rng, SeededRng, WallClock};

/// Extension trait adding async sleep to `Clock`.
///
/// This is separate from the base `Clock` trait because async methods
/// cannot be in traits without additional machinery, and we want to keep
/// `telltale-types` dependency-free.
pub trait AsyncClock: Clock {
    /// Sleep for a duration asynchronously.
    ///
    /// In simulation mode this may advance simulated time immediately.
    fn sleep(&self, duration: Duration) -> impl std::future::Future<Output = ()> + Send;
}

/// Implement `AsyncClock` for `MockClock`.
///
/// Sleep immediately advances simulated time without blocking.
impl AsyncClock for MockClock {
    async fn sleep(&self, duration: Duration) {
        self.advance(duration);
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
    fn test_mock_clock_advance() {
        let clock = MockClock::new();
        let start = clock.now();

        clock.advance(Duration::from_secs(1));
        assert!(clock.elapsed(start) >= Duration::from_secs(1));

        clock.advance(Duration::from_millis(500));
        assert!(clock.elapsed(start) >= Duration::from_millis(1500));
    }

    #[test]
    fn test_mock_wall_clock() {
        let clock = MockClock::new();
        assert_eq!(clock.now_unix_ns(), 0);
        clock.advance(Duration::from_millis(2));
        assert_eq!(clock.now_unix_ns(), 2_000_000);
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
    fn test_rng_duration_between() {
        let mut rng = SeededRng::new(42);
        let min = Duration::from_millis(100);
        let max = Duration::from_millis(200);

        for _ in 0..100 {
            let d = rng.duration_between(min, max);
            assert!(d >= min && d < max);
        }
    }
}
