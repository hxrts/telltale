//! Effect handler trait for the VM.
//!
//! The host (simulator, application, etc.) implements this trait to provide
//! material-specific behavior: computing payloads for sends, processing
//! received values, and performing integration steps.

use crate::coroutine::Value;

/// VM-level effect handler.
///
/// This is the interface between the VM and the host application. Each
/// choreography can bind a different handler at session open time.
pub trait EffectHandler {
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
}
