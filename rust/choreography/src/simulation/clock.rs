//! Clock and RNG traits for deterministic execution
//!
//! These traits allow protocol execution to be fully deterministic
//! by injecting time and randomness sources.

use std::time::{Duration, Instant};

/// Trait for time operations in protocol execution.
///
/// Implementations can provide real system time or simulated time
/// for deterministic replay and testing.
pub trait Clock: Send + Sync {
    /// Get the current instant.
    fn now(&self) -> Instant;

    /// Sleep for a duration.
    ///
    /// In simulation mode, this may advance simulated time instantly.
    fn sleep(&self, duration: Duration) -> impl std::future::Future<Output = ()> + Send;

    /// Get elapsed time since a previous instant.
    fn elapsed(&self, since: Instant) -> Duration {
        self.now().duration_since(since)
    }
}

/// System clock using real time.
#[derive(Debug, Clone, Copy, Default)]
pub struct SystemClock;

impl Clock for SystemClock {
    fn now(&self) -> Instant {
        Instant::now()
    }

    async fn sleep(&self, duration: Duration) {
        tokio::time::sleep(duration).await;
    }
}

/// Mock clock for testing with controllable time.
#[derive(Debug)]
pub struct MockClock {
    /// The simulated current time as an offset from the start instant.
    offset: std::sync::atomic::AtomicU64,
    /// The start instant (real time when MockClock was created).
    start: Instant,
}

impl MockClock {
    /// Create a new mock clock starting at the current instant.
    #[must_use]
    pub fn new() -> Self {
        Self {
            offset: std::sync::atomic::AtomicU64::new(0),
            start: Instant::now(),
        }
    }

    /// Advance the clock by a duration.
    pub fn advance(&self, duration: Duration) {
        self.offset.fetch_add(
            duration.as_nanos() as u64,
            std::sync::atomic::Ordering::SeqCst,
        );
    }

    /// Set the clock to a specific offset from start.
    pub fn set_offset(&self, offset: Duration) {
        self.offset.store(
            offset.as_nanos() as u64,
            std::sync::atomic::Ordering::SeqCst,
        );
    }

    /// Get the current offset.
    #[must_use]
    pub fn offset(&self) -> Duration {
        Duration::from_nanos(self.offset.load(std::sync::atomic::Ordering::SeqCst))
    }
}

impl Default for MockClock {
    fn default() -> Self {
        Self::new()
    }
}

impl Clock for MockClock {
    fn now(&self) -> Instant {
        // Return start + offset
        // Note: We can't actually create arbitrary Instants, so we use a workaround
        self.start + self.offset()
    }

    async fn sleep(&self, duration: Duration) {
        // In mock mode, we just advance time instantly
        self.advance(duration);
    }
}

/// Trait for random number generation in protocol execution.
///
/// Implementations can provide real randomness or seeded/deterministic
/// values for reproducible testing.
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

    /// Generate a random f64 in [0, 1).
    fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }

    /// Choose a random element from a slice.
    fn choose<'a, T>(&mut self, slice: &'a [T]) -> Option<&'a T> {
        if slice.is_empty() {
            None
        } else {
            Some(&slice[self.next_u64() as usize % slice.len()])
        }
    }

    /// Generate a random duration between min and max.
    fn duration_between(&mut self, min: Duration, max: Duration) -> Duration {
        let min_nanos = min.as_nanos() as u64;
        let max_nanos = max.as_nanos() as u64;
        if max_nanos <= min_nanos {
            return min;
        }
        let range = max_nanos - min_nanos;
        Duration::from_nanos(min_nanos + (self.next_u64() % range))
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
    /// Create a new seeded RNG.
    #[must_use]
    pub fn new(seed: u64) -> Self {
        // Ensure non-zero state
        Self {
            state: if seed == 0 { 1 } else { seed },
        }
    }

    /// Create from current time (non-deterministic).
    #[must_use]
    pub fn from_time() -> Self {
        Self::new(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
        )
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
        // xorshift64
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state
    }
}

/// System RNG using thread_rng (non-deterministic).
#[derive(Debug, Default)]
pub struct SystemRng;

impl Rng for SystemRng {
    fn next_u64(&mut self) -> u64 {
        // Use a simple hash of current time + memory address for randomness
        // In production, you'd want to use rand crate
        let ptr = self as *mut Self as u64;
        let time = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64;
        ptr.wrapping_mul(time).wrapping_add(0x517cc1b727220a95)
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

        // Different seeds should produce different sequences
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
    fn test_rng_choose() {
        let mut rng = SeededRng::new(42);
        let items = vec![1, 2, 3, 4, 5];

        let chosen = rng.choose(&items);
        assert!(chosen.is_some());
        assert!(items.contains(chosen.unwrap()));
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
