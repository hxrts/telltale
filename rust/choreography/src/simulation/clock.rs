//! Clock and RNG traits for deterministic simulation.
//!
//! This module provides injected time and randomness primitives for replayable
//! simulation contexts. Production code can use runtime implementations that
//! satisfy these traits but source values from host APIs.

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use telltale_types::FixedQ32;

/// Trait for monotonic time in protocol execution.
///
/// `now()` is measured as a monotonic offset from an injected epoch.
pub trait Clock: Send + Sync {
    /// Get the current monotonic offset.
    fn now(&self) -> Duration;

    /// Sleep for a duration.
    ///
    /// In simulation mode this may advance simulated time immediately.
    fn sleep(&self, duration: Duration) -> impl std::future::Future<Output = ()> + Send;

    /// Get elapsed time since a previous monotonic point.
    fn elapsed(&self, since: Duration) -> Duration {
        self.now().saturating_sub(since)
    }
}

/// Trait for wall-clock timestamps used in metadata (for example envelope time).
pub trait WallClock: Send + Sync {
    /// Current wall-clock timestamp in nanoseconds since Unix epoch.
    fn now_unix_ns(&self) -> u64;
}

/// Mock monotonic and wall clock for deterministic testing.
///
/// Time is represented as a controllable nanosecond counter. No host clock
/// calls are used.
#[derive(Debug)]
pub struct MockClock {
    /// Current simulated offset in nanoseconds.
    offset_ns: AtomicU64,
}

impl MockClock {
    /// Create a new mock clock at offset zero.
    #[must_use]
    pub fn new() -> Self {
        Self {
            offset_ns: AtomicU64::new(0),
        }
    }

    /// Advance the clock by a duration.
    pub fn advance(&self, duration: Duration) {
        let delta = u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX);
        // Ignore result: fetch_update always succeeds when closure returns Some
        match self
            .offset_ns
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
                Some(current.saturating_add(delta))
            }) {
            Ok(_) | Err(_) => {}
        }
    }

    /// Set the clock to a specific offset from epoch.
    pub fn set_offset(&self, offset: Duration) {
        let offset_ns = u64::try_from(offset.as_nanos()).unwrap_or(u64::MAX);
        self.offset_ns.store(offset_ns, Ordering::SeqCst);
    }

    /// Get the current offset.
    #[must_use]
    pub fn offset(&self) -> Duration {
        Duration::from_nanos(self.offset_ns.load(Ordering::SeqCst))
    }
}

impl Default for MockClock {
    fn default() -> Self {
        Self::new()
    }
}

impl Clock for MockClock {
    fn now(&self) -> Duration {
        self.offset()
    }

    async fn sleep(&self, duration: Duration) {
        self.advance(duration);
    }
}

impl WallClock for MockClock {
    fn now_unix_ns(&self) -> u64 {
        self.offset_ns.load(Ordering::SeqCst)
    }
}

/// Trait for random number generation in protocol execution.
///
/// Implementations can provide deterministic seeded values for reproducible
/// testing or host entropy in runtime contexts.
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

    /// Generate a random fixed-point value in [0, 1).
    fn next_f64(&mut self) -> FixedQ32 {
        // FixedQ32 is Q32.32: value = bits / 2^32
        // Take upper 32 bits as fractional part to get value in [0, 1)
        let frac_bits = (self.next_u64() >> 32) as i64;
        FixedQ32::from_bits(frac_bits)
    }

    /// Choose a random element from a slice.
    fn choose<'a, T>(&mut self, slice: &'a [T]) -> Option<&'a T> {
        if slice.is_empty() {
            return None;
        }
        let len = u64::try_from(slice.len()).ok()?;
        let idx = self.next_u64() % len;
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
        Duration::from_nanos(min_ns + (self.next_u64() % range))
    }
}

/// Seeded RNG for reproducible randomness.
///
/// Uses a simple xorshift64 algorithm for fast, reproducible random numbers.
#[derive(Debug, Clone)]
pub struct SeededRng {
    state: u64,
}

impl SeededRng {
    /// Create a new seeded RNG with an explicit seed.
    ///
    /// For deterministic simulation, always use explicit seeds.
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
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state
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
