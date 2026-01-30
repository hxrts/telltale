//! Actions in Session Types
//!
//! Actions represent the basic communication primitives in session types.
//! These correspond to the Lean definitions in `lean/Telltale/Protocol/Core.lean`.

use crate::Label;
use serde::{Deserialize, Serialize};

/// Basic action type (send or receive).
///
/// Corresponds to Lean's action polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Action {
    /// Send action (internal choice, output)
    Send,
    /// Receive action (external choice, input)
    Recv,
}

impl Action {
    /// Get the dual action
    #[must_use]
    pub fn dual(&self) -> Self {
        match self {
            Action::Send => Action::Recv,
            Action::Recv => Action::Send,
        }
    }

    /// Check if this is a send action
    #[must_use]
    pub fn is_send(&self) -> bool {
        matches!(self, Action::Send)
    }

    /// Check if this is a receive action
    #[must_use]
    pub fn is_recv(&self) -> bool {
        matches!(self, Action::Recv)
    }
}

impl std::fmt::Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Action::Send => write!(f, "!"),
            Action::Recv => write!(f, "?"),
        }
    }
}

/// A complete local action with role and label.
///
/// Represents a single communication step: action + partner + message.
/// Corresponds to Lean's action representation in traces.
///
/// # Examples
///
/// ```
/// use telltale_types::{LocalAction, Action, Label};
///
/// // Send "hello" to role B
/// let action = LocalAction::new(Action::Send, "B", Label::new("hello"));
/// assert!(action.is_send());
/// assert_eq!(action.partner(), "B");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LocalAction {
    /// The action type (send or receive)
    action: Action,
    /// The communication partner
    partner: String,
    /// The message label
    label: Label,
}

impl LocalAction {
    /// Create a new local action
    #[must_use]
    pub fn new(action: Action, partner: impl Into<String>, label: Label) -> Self {
        Self {
            action,
            partner: partner.into(),
            label,
        }
    }

    /// Create a send action
    #[must_use]
    pub fn send(partner: impl Into<String>, label: Label) -> Self {
        Self::new(Action::Send, partner, label)
    }

    /// Create a receive action
    #[must_use]
    pub fn recv(partner: impl Into<String>, label: Label) -> Self {
        Self::new(Action::Recv, partner, label)
    }

    /// Get the action type
    #[must_use]
    pub fn action(&self) -> Action {
        self.action
    }

    /// Get the partner role
    #[must_use]
    pub fn partner(&self) -> &str {
        &self.partner
    }

    /// Get the message label
    #[must_use]
    pub fn label(&self) -> &Label {
        &self.label
    }

    /// Check if this is a send action
    #[must_use]
    pub fn is_send(&self) -> bool {
        self.action.is_send()
    }

    /// Check if this is a receive action
    #[must_use]
    pub fn is_recv(&self) -> bool {
        self.action.is_recv()
    }

    /// Get the dual action (swap send/recv, keep partner and label)
    #[must_use]
    pub fn dual(&self) -> Self {
        Self {
            action: self.action.dual(),
            partner: self.partner.clone(),
            label: self.label.clone(),
        }
    }
}

impl std::fmt::Display for LocalAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}{{{}}}", self.action, self.partner, self.label)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_action_dual() {
        assert_eq!(Action::Send.dual(), Action::Recv);
        assert_eq!(Action::Recv.dual(), Action::Send);
    }

    #[test]
    fn test_action_display() {
        assert_eq!(format!("{}", Action::Send), "!");
        assert_eq!(format!("{}", Action::Recv), "?");
    }

    #[test]
    fn test_local_action_new() {
        let action = LocalAction::new(Action::Send, "B", Label::new("msg"));
        assert!(action.is_send());
        assert_eq!(action.partner(), "B");
        assert_eq!(action.label().name, "msg");
    }

    #[test]
    fn test_local_action_send_recv() {
        let send = LocalAction::send("B", Label::new("hello"));
        let recv = LocalAction::recv("A", Label::new("world"));

        assert!(send.is_send());
        assert!(!send.is_recv());
        assert!(recv.is_recv());
        assert!(!recv.is_send());
    }

    #[test]
    fn test_local_action_dual() {
        let send = LocalAction::send("B", Label::new("msg"));
        let recv = send.dual();

        assert!(recv.is_recv());
        assert_eq!(recv.partner(), "B");
        assert_eq!(recv.label().name, "msg");
    }

    #[test]
    fn test_local_action_display() {
        let action = LocalAction::send("B", Label::new("hello"));
        assert_eq!(format!("{}", action), "!B{hello}");

        let recv = LocalAction::recv("A", Label::new("data"));
        assert_eq!(format!("{}", recv), "?A{data}");
    }
}
