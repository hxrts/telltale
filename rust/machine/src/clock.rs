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

/// Finite Rust representation cannot admit another mathematical model round.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum ClockExhaustion {
    /// The logical round counter has no successor.
    #[error("simulation tick counter exhausted")]
    Tick,
    /// The simulated duration has no representable successor.
    #[error("simulation duration exhausted")]
    Duration,
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

    /// Admit exactly one scheduler round, atomically.
    ///
    /// # Errors
    /// Returns typed exhaustion without changing either counter.
    pub fn advance(&mut self) -> Result<(), ClockExhaustion> {
        let tick = self.tick.checked_add(1).ok_or(ClockExhaustion::Tick)?;
        let time = self
            .time
            .checked_add(self.tick_duration)
            .ok_or(ClockExhaustion::Duration)?;
        self.tick = tick;
        self.time = time;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn tick_exhaustion_preserves_both_original_counters() {
        let mut clock = SimClock {
            tick: u64::MAX,
            time: Duration::from_secs(3),
            tick_duration: Duration::from_secs(1),
        };
        assert_eq!(clock.advance(), Err(ClockExhaustion::Tick));
        assert_eq!(clock.tick, u64::MAX);
        assert_eq!(clock.time, Duration::from_secs(3));
    }
    #[test]
    fn duration_exhaustion_does_not_partially_advance_tick() {
        let mut clock = SimClock {
            tick: 7,
            time: Duration::MAX,
            tick_duration: Duration::from_nanos(1),
        };
        assert_eq!(clock.advance(), Err(ClockExhaustion::Duration));
        assert_eq!(clock.tick, 7);
        assert_eq!(clock.time, Duration::MAX);
    }
    #[test]
    fn final_representable_round_advances_exactly_once_then_refuses() {
        let mut clock = SimClock {
            tick: u64::MAX - 1,
            time: Duration::MAX - Duration::from_nanos(1),
            tick_duration: Duration::from_nanos(1),
        };
        assert_eq!(clock.advance(), Ok(()));
        assert_eq!(clock.tick, u64::MAX);
        assert_eq!(clock.time, Duration::MAX);
        assert_eq!(clock.advance(), Err(ClockExhaustion::Tick));
        assert_eq!(clock.time, Duration::MAX);
    }
}
