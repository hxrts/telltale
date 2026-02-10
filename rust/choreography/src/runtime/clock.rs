//! System clock and RNG for production runtime
//!
//! These implementations use real system time and entropy sources.
//! For deterministic simulation and testing, use the mock implementations
//! in the `testing` module instead.

use std::time::{Duration, Instant};

use crate::testing::clock::{AsyncClock, Clock, Rng, WallClock};

/// System clock using real time.
///
/// This implementation is non-deterministic and should only be used
/// in production runtime contexts, not in simulation or replay scenarios.
#[derive(Debug, Clone, Copy, Default)]
pub struct SystemClock;

impl SystemClock {
    /// Get the current wall-clock time as nanoseconds since Unix epoch.
    ///
    /// Use this with `EnvelopeBuilder::timestamp()` when you need real timestamps
    /// in production contexts.
    #[must_use]
    pub fn timestamp_ns() -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64
    }
}

impl Clock for SystemClock {
    fn now(&self) -> Duration {
        static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
        START.get_or_init(Instant::now).elapsed()
    }

    fn advance(&self, _duration: Duration) {
        // Real clock cannot be advanced; this is a no-op
    }
}

impl AsyncClock for SystemClock {
    async fn sleep(&self, duration: Duration) {
        #[cfg(not(target_arch = "wasm32"))]
        {
            tokio::time::sleep(duration).await;
        }
        #[cfg(target_arch = "wasm32")]
        {
            wasm_timer::Delay::new(duration).await.ok();
        }
    }
}

impl WallClock for SystemClock {
    fn now_unix_ns(&self) -> u64 {
        Self::timestamp_ns()
    }
}

/// System RNG using host entropy (non-deterministic).
///
/// This implementation uses system time and memory addresses for entropy.
/// For reproducible testing, use `SeededRng` instead.
#[derive(Debug, Default)]
pub struct SystemRng {
    state: u64,
}

impl SystemRng {
    /// Create a new system RNG seeded from current time.
    #[must_use]
    pub fn new() -> Self {
        let seed = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64;
        Self {
            state: if seed == 0 { 1 } else { seed },
        }
    }
}

impl Rng for SystemRng {
    fn next_u64(&mut self) -> u64 {
        // Mix in address for additional entropy
        let ptr = self as *mut Self as u64;
        self.state = self
            .state
            .wrapping_mul(ptr)
            .wrapping_add(0x517cc1b727220a95);
        // xorshift64 for the output
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state
    }

    fn fork(&mut self) -> Self {
        // Fork by mixing current state with time-based entropy
        let fork_seed = self.next_u64()
            ^ std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64;
        Self {
            state: if fork_seed == 0 { 1 } else { fork_seed },
        }
    }
}
