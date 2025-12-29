//! Protocol observer trait for monitoring execution
//!
//! Observers receive callbacks during protocol execution, enabling
//! logging, metrics collection, and simulation control.

use crate::effects::ChoreographyError;

/// Trait for observing protocol execution events.
///
/// Implementations can log events, collect metrics, or control
/// simulation behavior based on observed events.
pub trait ProtocolObserver: Send {
    /// Called when a protocol phase starts.
    fn on_phase_start(&mut self, protocol: &str, role: &str, phase: &str);

    /// Called when a protocol phase ends.
    fn on_phase_end(&mut self, protocol: &str, role: &str, phase: &str);

    /// Called when a message is sent.
    fn on_send(&mut self, from: &str, to: &str, msg_type: &str, size: usize);

    /// Called when a message is received.
    fn on_recv(&mut self, from: &str, to: &str, msg_type: &str, size: usize);

    /// Called when a choice is made (internal choice).
    fn on_choice(&mut self, decider: &str, branch: &str);

    /// Called when a choice is received (external choice).
    fn on_offer(&mut self, from: &str, branch: &str);

    /// Called when an error occurs.
    fn on_error(&mut self, protocol: &str, role: &str, error: &ChoreographyError);

    /// Called when the protocol completes successfully.
    fn on_complete(&mut self, protocol: &str, role: &str);
}

/// A null observer that does nothing.
///
/// Use this when you don't need to observe protocol execution.
#[derive(Debug, Default, Clone, Copy)]
pub struct NullObserver;

impl ProtocolObserver for NullObserver {
    fn on_phase_start(&mut self, _protocol: &str, _role: &str, _phase: &str) {}
    fn on_phase_end(&mut self, _protocol: &str, _role: &str, _phase: &str) {}
    fn on_send(&mut self, _from: &str, _to: &str, _msg_type: &str, _size: usize) {}
    fn on_recv(&mut self, _from: &str, _to: &str, _msg_type: &str, _size: usize) {}
    fn on_choice(&mut self, _decider: &str, _branch: &str) {}
    fn on_offer(&mut self, _from: &str, _branch: &str) {}
    fn on_error(&mut self, _protocol: &str, _role: &str, _error: &ChoreographyError) {}
    fn on_complete(&mut self, _protocol: &str, _role: &str) {}
}

/// An event that occurred during protocol execution.
#[derive(Debug, Clone)]
pub enum ProtocolEvent {
    /// A phase started.
    PhaseStart {
        protocol: String,
        role: String,
        phase: String,
    },
    /// A phase ended.
    PhaseEnd {
        protocol: String,
        role: String,
        phase: String,
    },
    /// A message was sent.
    Send {
        from: String,
        to: String,
        msg_type: String,
        size: usize,
    },
    /// A message was received.
    Recv {
        from: String,
        to: String,
        msg_type: String,
        size: usize,
    },
    /// A choice was made.
    Choice { decider: String, branch: String },
    /// A choice was received.
    Offer { from: String, branch: String },
    /// An error occurred.
    Error {
        protocol: String,
        role: String,
        error: String,
    },
    /// Protocol completed.
    Complete { protocol: String, role: String },
}

/// A recording observer that stores all events.
///
/// Useful for testing and debugging protocol execution.
#[derive(Debug, Default)]
pub struct RecordingObserver {
    events: Vec<ProtocolEvent>,
}

impl RecordingObserver {
    /// Create a new recording observer.
    #[must_use]
    pub fn new() -> Self {
        Self { events: Vec::new() }
    }

    /// Get all recorded events.
    #[must_use]
    pub fn events(&self) -> &[ProtocolEvent] {
        &self.events
    }

    /// Take all recorded events, clearing the observer.
    pub fn take_events(&mut self) -> Vec<ProtocolEvent> {
        std::mem::take(&mut self.events)
    }

    /// Clear all recorded events.
    pub fn clear(&mut self) {
        self.events.clear();
    }

    /// Get the number of recorded events.
    #[must_use]
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Check if no events have been recorded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Get send events only.
    pub fn sends(&self) -> impl Iterator<Item = &ProtocolEvent> {
        self.events
            .iter()
            .filter(|e| matches!(e, ProtocolEvent::Send { .. }))
    }

    /// Get recv events only.
    pub fn recvs(&self) -> impl Iterator<Item = &ProtocolEvent> {
        self.events
            .iter()
            .filter(|e| matches!(e, ProtocolEvent::Recv { .. }))
    }

    /// Get error events only.
    pub fn errors(&self) -> impl Iterator<Item = &ProtocolEvent> {
        self.events
            .iter()
            .filter(|e| matches!(e, ProtocolEvent::Error { .. }))
    }
}

impl ProtocolObserver for RecordingObserver {
    fn on_phase_start(&mut self, protocol: &str, role: &str, phase: &str) {
        self.events.push(ProtocolEvent::PhaseStart {
            protocol: protocol.to_string(),
            role: role.to_string(),
            phase: phase.to_string(),
        });
    }

    fn on_phase_end(&mut self, protocol: &str, role: &str, phase: &str) {
        self.events.push(ProtocolEvent::PhaseEnd {
            protocol: protocol.to_string(),
            role: role.to_string(),
            phase: phase.to_string(),
        });
    }

    fn on_send(&mut self, from: &str, to: &str, msg_type: &str, size: usize) {
        self.events.push(ProtocolEvent::Send {
            from: from.to_string(),
            to: to.to_string(),
            msg_type: msg_type.to_string(),
            size,
        });
    }

    fn on_recv(&mut self, from: &str, to: &str, msg_type: &str, size: usize) {
        self.events.push(ProtocolEvent::Recv {
            from: from.to_string(),
            to: to.to_string(),
            msg_type: msg_type.to_string(),
            size,
        });
    }

    fn on_choice(&mut self, decider: &str, branch: &str) {
        self.events.push(ProtocolEvent::Choice {
            decider: decider.to_string(),
            branch: branch.to_string(),
        });
    }

    fn on_offer(&mut self, from: &str, branch: &str) {
        self.events.push(ProtocolEvent::Offer {
            from: from.to_string(),
            branch: branch.to_string(),
        });
    }

    fn on_error(&mut self, protocol: &str, role: &str, error: &ChoreographyError) {
        self.events.push(ProtocolEvent::Error {
            protocol: protocol.to_string(),
            role: role.to_string(),
            error: error.to_string(),
        });
    }

    fn on_complete(&mut self, protocol: &str, role: &str) {
        self.events.push(ProtocolEvent::Complete {
            protocol: protocol.to_string(),
            role: role.to_string(),
        });
    }
}

/// A multiplexing observer that forwards events to multiple observers.
pub struct MultiObserver<'a> {
    observers: Vec<&'a mut dyn ProtocolObserver>,
}

impl<'a> MultiObserver<'a> {
    /// Create a new multi-observer.
    pub fn new(observers: Vec<&'a mut dyn ProtocolObserver>) -> Self {
        Self { observers }
    }
}

impl ProtocolObserver for MultiObserver<'_> {
    fn on_phase_start(&mut self, protocol: &str, role: &str, phase: &str) {
        for obs in &mut self.observers {
            obs.on_phase_start(protocol, role, phase);
        }
    }

    fn on_phase_end(&mut self, protocol: &str, role: &str, phase: &str) {
        for obs in &mut self.observers {
            obs.on_phase_end(protocol, role, phase);
        }
    }

    fn on_send(&mut self, from: &str, to: &str, msg_type: &str, size: usize) {
        for obs in &mut self.observers {
            obs.on_send(from, to, msg_type, size);
        }
    }

    fn on_recv(&mut self, from: &str, to: &str, msg_type: &str, size: usize) {
        for obs in &mut self.observers {
            obs.on_recv(from, to, msg_type, size);
        }
    }

    fn on_choice(&mut self, decider: &str, branch: &str) {
        for obs in &mut self.observers {
            obs.on_choice(decider, branch);
        }
    }

    fn on_offer(&mut self, from: &str, branch: &str) {
        for obs in &mut self.observers {
            obs.on_offer(from, branch);
        }
    }

    fn on_error(&mut self, protocol: &str, role: &str, error: &ChoreographyError) {
        for obs in &mut self.observers {
            obs.on_error(protocol, role, error);
        }
    }

    fn on_complete(&mut self, protocol: &str, role: &str) {
        for obs in &mut self.observers {
            obs.on_complete(protocol, role);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_null_observer() {
        let mut obs = NullObserver;
        // Should not panic
        obs.on_phase_start("Proto", "Role", "Phase");
        obs.on_send("A", "B", "Msg", 100);
    }

    #[test]
    fn test_recording_observer() {
        let mut obs = RecordingObserver::new();

        obs.on_phase_start("Proto", "Client", "handshake");
        obs.on_send("Client", "Server", "Request", 50);
        obs.on_recv("Server", "Client", "Response", 100);
        obs.on_phase_end("Proto", "Client", "handshake");

        assert_eq!(obs.len(), 4);
        assert_eq!(obs.sends().count(), 1);
        assert_eq!(obs.recvs().count(), 1);
    }

    #[test]
    fn test_recording_observer_take() {
        let mut obs = RecordingObserver::new();
        obs.on_send("A", "B", "Msg", 10);

        let events = obs.take_events();
        assert_eq!(events.len(), 1);
        assert!(obs.is_empty());
    }
}
