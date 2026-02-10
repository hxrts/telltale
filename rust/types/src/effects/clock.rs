//! Clock traits for deterministic time management.
//!
//! Provides monotonic and wall-clock abstractions that can be implemented
//! by either mock clocks (for testing) or real clocks (for production).

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

/// Trait for monotonic time in protocol execution.
///
/// Time is measured as a monotonic offset from an arbitrary epoch.
/// This trait is synchronous; async extensions are provided by downstream crates.
pub trait Clock: Send + Sync {
    /// Get the current monotonic offset.
    fn now(&self) -> Duration;

    /// Advance simulated time by a duration.
    ///
    /// For real clocks, this may be a no-op. For mock clocks, this
    /// immediately advances the internal counter.
    fn advance(&self, duration: Duration);

    /// Get elapsed time since a previous monotonic point.
    fn elapsed(&self, since: Duration) -> Duration {
        self.now().saturating_sub(since)
    }
}

/// Trait for wall-clock timestamps used in metadata.
///
/// Wall-clock time is used for envelope timestamps, logging, and other
/// contexts where absolute time matters. Unlike monotonic time, wall-clock
/// time can jump (e.g., NTP adjustments).
pub trait WallClock: Send + Sync {
    /// Current wall-clock timestamp in nanoseconds since Unix epoch.
    fn now_unix_ns(&self) -> u64;
}

/// Mock clock for deterministic testing.
///
/// Time is represented as a controllable nanosecond counter. No host clock
/// calls are used, making execution fully reproducible.
///
/// # Thread Safety
///
/// `MockClock` uses atomic operations and can be safely shared across threads.
///
/// # Example
///
/// ```
/// use std::time::Duration;
/// use telltale_types::effects::{Clock, MockClock};
///
/// let clock = MockClock::new();
/// assert_eq!(clock.now(), Duration::ZERO);
///
/// clock.advance(Duration::from_secs(1));
/// assert_eq!(clock.now(), Duration::from_secs(1));
/// ```
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

    /// Set the clock to a specific offset from epoch.
    pub fn set_offset(&self, offset: Duration) {
        let offset_ns = u64::try_from(offset.as_nanos()).unwrap_or(u64::MAX);
        self.offset_ns.store(offset_ns, Ordering::SeqCst);
    }

    /// Get the current offset as raw nanoseconds.
    #[must_use]
    pub fn offset_ns(&self) -> u64 {
        self.offset_ns.load(Ordering::SeqCst)
    }
}

impl Default for MockClock {
    fn default() -> Self {
        Self::new()
    }
}

impl Clock for MockClock {
    fn now(&self) -> Duration {
        Duration::from_nanos(self.offset_ns.load(Ordering::SeqCst))
    }

    fn advance(&self, duration: Duration) {
        let delta = u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX);
        // fetch_update with a closure that always returns Some always succeeds
        let _ = self
            .offset_ns
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
                Some(current.saturating_add(delta))
            });
    }
}

impl WallClock for MockClock {
    fn now_unix_ns(&self) -> u64 {
        self.offset_ns.load(Ordering::SeqCst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mock_clock_starts_at_zero() {
        let clock = MockClock::new();
        assert_eq!(clock.now(), Duration::ZERO);
    }

    #[test]
    fn test_mock_clock_advance() {
        let clock = MockClock::new();
        let start = clock.now();

        clock.advance(Duration::from_secs(1));
        assert_eq!(clock.elapsed(start), Duration::from_secs(1));

        clock.advance(Duration::from_millis(500));
        assert_eq!(clock.elapsed(start), Duration::from_millis(1500));
    }

    #[test]
    fn test_mock_clock_set_offset() {
        let clock = MockClock::new();
        clock.set_offset(Duration::from_secs(100));
        assert_eq!(clock.now(), Duration::from_secs(100));
    }

    #[test]
    fn test_mock_wall_clock() {
        let clock = MockClock::new();
        assert_eq!(clock.now_unix_ns(), 0);
        clock.advance(Duration::from_millis(2));
        assert_eq!(clock.now_unix_ns(), 2_000_000);
    }
}
