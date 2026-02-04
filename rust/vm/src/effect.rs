//! Effect handler trait for the VM.
//!
//! The host (simulator, application, etc.) implements this trait to provide
//! material-specific behavior: computing payloads for sends, processing
//! received values, and performing integration steps.
//!
//! This is intentionally **not** the same as `telltale_choreography::ChoreoHandler`:
//! the VM handler is synchronous, session-local, and operates on bytecode state,
//! while `ChoreoHandler` is an async, typed transport abstraction for generated
//! choreography code.

use crate::coroutine::Value;
use crate::session::SessionId;

/// Decision returned by [`EffectHandler::send_decision`].
#[derive(Debug, Clone)]
pub enum SendDecision {
    /// Deliver the payload immediately (enqueue to buffer).
    Deliver(Value),
    /// Drop the message (sender still advances).
    Drop,
    /// Defer delivery (message handled by middleware).
    Defer,
}

/// Decision returned by [`EffectHandler::handle_acquire`].
#[derive(Debug, Clone)]
pub enum AcquireDecision {
    /// Acquire succeeded and produced evidence.
    Grant(Value),
    /// Acquire denied and should block.
    Block,
}

/// VM-level effect handler.
///
/// This is the interface between the VM and the host application. Each
/// choreography can bind a different handler at session open time.
pub trait EffectHandler: Send + Sync {
    /// Compute the payload for a send instruction.
    ///
    /// # Arguments
    /// * `role` - The sending role
    /// * `partner` - The receiving role
    /// * `label` - The message label
    /// * `state` - The coroutine's register file (for reading state)
    ///
    /// # Errors
    /// Returns an error string if the handler fails.
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> Result<Value, String>;

    /// Decide how to handle a send, optionally with a precomputed payload.
    ///
    /// Middleware can override this to model loss/delay/corruption. The default
    /// behavior computes a payload via `handle_send` unless one is provided.
    ///
    /// # Errors
    ///
    /// Returns an error string if the handler fails.
    #[allow(clippy::too_many_arguments)]
    fn send_decision(
        &self,
        _sid: SessionId,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        if let Some(payload) = payload {
            Ok(SendDecision::Deliver(payload))
        } else {
            self.handle_send(role, partner, label, state)
                .map(SendDecision::Deliver)
        }
    }

    /// Process a received value.
    ///
    /// # Arguments
    /// * `role` - The receiving role
    /// * `partner` - The sending role
    /// * `label` - The message label
    /// * `state` - The coroutine's register file (mutable for state updates)
    /// * `payload` - The received value
    ///
    /// # Errors
    /// Returns an error string if the handler fails.
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String>;

    /// Choose which branch to take for internal choice (select).
    ///
    /// Called when executing a multi-branch Send (internal choice). The handler
    /// receives the available labels and returns the chosen one. Matches the Lean
    /// `stepChoose` semantics where the handler/process decides which label to select.
    ///
    /// # Arguments
    /// * `role` - The choosing role
    /// * `partner` - The partner role
    /// * `labels` - The available branch labels
    /// * `state` - The coroutine's register file (for reading state)
    ///
    /// # Errors
    /// Returns an error string if the handler fails.
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> Result<String, String>;

    /// Perform an integration step after a protocol round.
    ///
    /// Called after all sends/receives for a tick are complete.
    ///
    /// # Errors
    /// Returns an error string if the handler fails.
    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String>;

    /// Attempt to acquire a guard layer.
    ///
    /// Returning `AcquireDecision::Block` causes the coroutine to block.
    ///
    /// # Errors
    ///
    /// Returns an error string if acquisition fails.
    fn handle_acquire(
        &self,
        _sid: SessionId,
        _role: &str,
        _layer: &str,
        _state: &[Value],
    ) -> Result<AcquireDecision, String> {
        Ok(AcquireDecision::Grant(Value::Unit))
    }

    /// Release a guard layer using previously acquired evidence.
    ///
    /// # Errors
    ///
    /// Returns an error string if release fails.
    fn handle_release(
        &self,
        _sid: SessionId,
        _role: &str,
        _layer: &str,
        _evidence: &Value,
        _state: &[Value],
    ) -> Result<(), String> {
        Ok(())
    }
}

impl<T: EffectHandler + ?Sized> EffectHandler for &T {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> Result<Value, String> {
        (**self).handle_send(role, partner, label, state)
    }

    fn send_decision(
        &self,
        sid: SessionId,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        (**self).send_decision(sid, role, partner, label, state, payload)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
        (**self).handle_recv(role, partner, label, state, payload)
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> Result<String, String> {
        (**self).handle_choose(role, partner, labels, state)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        (**self).step(role, state)
    }

    fn handle_acquire(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        state: &[Value],
    ) -> Result<AcquireDecision, String> {
        (**self).handle_acquire(sid, role, layer, state)
    }

    fn handle_release(
        &self,
        sid: SessionId,
        role: &str,
        layer: &str,
        evidence: &Value,
        state: &[Value],
    ) -> Result<(), String> {
        (**self).handle_release(sid, role, layer, evidence, state)
    }
}
