//! Deterministic simulation clock.

use serde::{Deserialize, Serialize};
use std::time::Duration;

/// Deterministic simulation clock.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimClock {
    /// Logical tick counter (increments once per scheduler round).
    pub tick: u64,
    /// Simulated time.
    pub time: Duration,
    /// Duration advanced per tick.
    pub tick_duration: Duration,
}

impl SimClock {
    /// Create a new clock starting at tick 0/time 0.
    #[must_use]
    pub fn new(tick_duration: Duration) -> Self {
        Self {
            tick: 0,
            time: Duration::from_secs(0),
            tick_duration,
        }
    }

    /// Advance the clock by one tick.
    pub fn advance(&mut self) {
        self.tick += 1;
        self.time += self.tick_duration;
    }
}
