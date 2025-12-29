//! Mermaid diagram format support for FSMs.
//!
//! This module provides export to Mermaid flowchart format.
//! Mermaid diagrams can be rendered in many documentation tools,
//! including GitHub, GitLab, and Notion.
//!
//! # Example
//!
//! ```rust
//! use rumpsteak_aura_fsm::{Fsm, Mermaid, MermaidConfig};
//!
//! let fsm: Fsm<&str, &str, &str> = Fsm::new("Client");
//! let mermaid = Mermaid::new(&fsm);
//! println!("{}", mermaid);
//! ```
//!
//! # Output Format
//!
//! The generated Mermaid diagram uses the flowchart syntax:
//!
//! ```text
//! flowchart LR
//!     0((0))
//!     1((1))
//!     0 -->|Server!Request| 1
//!     1 -->|Server?Response| 0
//! ```

use crate::Fsm;
use std::fmt::{self, Display, Formatter};

/// Configuration for Mermaid diagram generation.
#[derive(Debug, Clone)]
pub struct MermaidConfig {
    /// Direction of the flowchart (LR, RL, TB, BT).
    pub direction: MermaidDirection,
    /// Node shape style.
    pub node_style: NodeStyle,
    /// Whether to include the role name in the title.
    pub include_title: bool,
    /// Whether to use subgraphs for grouping.
    pub use_subgraphs: bool,
}

impl Default for MermaidConfig {
    fn default() -> Self {
        Self {
            direction: MermaidDirection::LeftToRight,
            node_style: NodeStyle::Circle,
            include_title: true,
            use_subgraphs: false,
        }
    }
}

/// Direction for Mermaid flowchart layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MermaidDirection {
    /// Left to Right
    LeftToRight,
    /// Right to Left
    RightToLeft,
    /// Top to Bottom
    TopToBottom,
    /// Bottom to Top
    BottomToTop,
}

impl Display for MermaidDirection {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            MermaidDirection::LeftToRight => write!(f, "LR"),
            MermaidDirection::RightToLeft => write!(f, "RL"),
            MermaidDirection::TopToBottom => write!(f, "TB"),
            MermaidDirection::BottomToTop => write!(f, "BT"),
        }
    }
}

/// Node shape style for Mermaid diagrams.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeStyle {
    /// Circle: ((text))
    Circle,
    /// Rectangle: [text]
    Rectangle,
    /// Rounded rectangle: (text)
    RoundedRect,
    /// Diamond: {text}
    Diamond,
    /// Stadium: ([text])
    Stadium,
}

impl NodeStyle {
    /// Get the opening delimiter for this node style.
    fn open(&self) -> &'static str {
        match self {
            NodeStyle::Circle => "((",
            NodeStyle::Rectangle => "[",
            NodeStyle::RoundedRect => "(",
            NodeStyle::Diamond => "{",
            NodeStyle::Stadium => "([",
        }
    }

    /// Get the closing delimiter for this node style.
    fn close(&self) -> &'static str {
        match self {
            NodeStyle::Circle => "))",
            NodeStyle::Rectangle => "]",
            NodeStyle::RoundedRect => ")",
            NodeStyle::Diamond => "}",
            NodeStyle::Stadium => "])",
        }
    }
}

/// Wrapper for exporting an FSM in Mermaid format.
///
/// Mermaid is a JavaScript-based diagramming tool that renders
/// Markdown-inspired text definitions into diagrams.
///
/// # Example
///
/// ```rust
/// use rumpsteak_aura_fsm::{Fsm, Mermaid};
///
/// let fsm: Fsm<&str, &str, &str> = Fsm::new("Client");
/// let mermaid = Mermaid::new(&fsm);
/// println!("{}", mermaid);
/// ```
pub struct Mermaid<'a, R, N, E> {
    fsm: &'a Fsm<R, N, E>,
    config: MermaidConfig,
}

impl<'a, R, N, E> Mermaid<'a, R, N, E> {
    /// Creates a new Mermaid exporter for the given FSM.
    pub fn new(fsm: &'a Fsm<R, N, E>) -> Self {
        Self {
            fsm,
            config: MermaidConfig::default(),
        }
    }

    /// Creates a new Mermaid exporter with custom configuration.
    pub fn with_config(fsm: &'a Fsm<R, N, E>, config: MermaidConfig) -> Self {
        Self { fsm, config }
    }

    /// Set the direction of the flowchart.
    pub fn direction(mut self, direction: MermaidDirection) -> Self {
        self.config.direction = direction;
        self
    }

    /// Set the node style.
    pub fn node_style(mut self, style: NodeStyle) -> Self {
        self.config.node_style = style;
        self
    }

    /// Set whether to include a title.
    pub fn include_title(mut self, include: bool) -> Self {
        self.config.include_title = include;
        self
    }
}

impl<R: Display, N: Display, E: Display> Display for Mermaid<'_, R, N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Write title/comment if configured
        if self.config.include_title {
            writeln!(f, "---")?;
            writeln!(f, "title: {}", self.fsm.role())?;
            writeln!(f, "---")?;
        }

        // Write flowchart header
        writeln!(f, "flowchart {}", self.config.direction)?;

        let (states, transitions) = self.fsm.size();
        let open = self.config.node_style.open();
        let close = self.config.node_style.close();

        // Write state definitions
        if states > 0 {
            for i in self.fsm.states() {
                let idx = i.index();
                writeln!(f, "    {idx}{open}S{idx}{close}")?;
            }
        }

        // Write transitions
        if transitions > 0 {
            writeln!(f)?;
            for (from, to, transition) in self.fsm.transitions() {
                let (from, to) = (from.index(), to.index());
                // Escape special characters in labels
                let label = escape_mermaid_label(&format!("{transition}"));
                writeln!(f, "    {from} -->|{label}| {to}")?;
            }
        }

        Ok(())
    }
}

/// Escape special characters for Mermaid labels.
fn escape_mermaid_label(s: &str) -> String {
    s.replace('"', "'")
        .replace('|', "\\|")
        .replace('[', "\\[")
        .replace(']', "\\]")
        .replace('{', "\\{")
        .replace('}', "\\}")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

/// Generate a Mermaid state diagram (alternative format).
///
/// State diagrams use different syntax than flowcharts and may
/// be more suitable for FSM visualization in some contexts.
pub struct MermaidStateDiagram<'a, R, N, E> {
    fsm: &'a Fsm<R, N, E>,
}

impl<'a, R, N, E> MermaidStateDiagram<'a, R, N, E> {
    /// Creates a new state diagram exporter.
    pub fn new(fsm: &'a Fsm<R, N, E>) -> Self {
        Self { fsm }
    }
}

impl<R: Display, N: Display, E: Display> Display for MermaidStateDiagram<'_, R, N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Write state diagram header
        writeln!(f, "---")?;
        writeln!(f, "title: {}", self.fsm.role())?;
        writeln!(f, "---")?;
        writeln!(f, "stateDiagram-v2")?;

        let (states, _) = self.fsm.size();

        // Write initial state pointer
        if states > 0 {
            writeln!(f, "    [*] --> s0")?;
        }

        // Write transitions
        for (from, to, transition) in self.fsm.transitions() {
            let label = escape_mermaid_label(&format!("{transition}"));
            writeln!(f, "    s{} --> s{}: {}", from.index(), to.index(), label)?;
        }

        // Mark terminal states (states with no outgoing transitions)
        for state in self.fsm.states() {
            let has_outgoing = self.fsm.transitions_from(state).next().is_some();
            if !has_outgoing {
                writeln!(f, "    s{} --> [*]", state.index())?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Action, Message, Transition};

    #[test]
    fn test_mermaid_empty() {
        let fsm: Fsm<&str, &str, &str> = Fsm::new("Client");
        let mermaid = Mermaid::new(&fsm);
        let output = format!("{}", mermaid);

        assert!(output.contains("flowchart LR"));
        assert!(output.contains("title: Client"));
    }

    #[test]
    fn test_mermaid_with_states() {
        let mut fsm: Fsm<&str, &str, &str> = Fsm::new("Client");
        let s0 = fsm.add_state();
        let s1 = fsm.add_state();

        let transition = Transition::new("Server", Action::Output, Message::from_label("Hello"));
        fsm.add_transition(s0, s1, transition).unwrap();

        let mermaid = Mermaid::new(&fsm);
        let output = format!("{}", mermaid);

        assert!(output.contains("0((S0))"));
        assert!(output.contains("1((S1))"));
        assert!(output.contains("-->|"));
        assert!(output.contains("Hello"));
    }

    #[test]
    fn test_mermaid_direction() {
        let fsm: Fsm<&str, &str, &str> = Fsm::new("Client");
        let mermaid = Mermaid::new(&fsm).direction(MermaidDirection::TopToBottom);
        let output = format!("{}", mermaid);

        assert!(output.contains("flowchart TB"));
    }

    #[test]
    fn test_mermaid_node_style() {
        let mut fsm: Fsm<&str, &str, &str> = Fsm::new("Client");
        fsm.add_state();

        let mermaid = Mermaid::new(&fsm).node_style(NodeStyle::Rectangle);
        let output = format!("{}", mermaid);

        assert!(output.contains("[S0]"));
    }

    #[test]
    fn test_state_diagram() {
        let mut fsm: Fsm<&str, &str, &str> = Fsm::new("Client");
        let s0 = fsm.add_state();
        let s1 = fsm.add_state();

        let transition = Transition::new("Server", Action::Output, Message::from_label("Ping"));
        fsm.add_transition(s0, s1, transition).unwrap();

        let diagram = MermaidStateDiagram::new(&fsm);
        let output = format!("{}", diagram);

        assert!(output.contains("stateDiagram-v2"));
        assert!(output.contains("[*] --> s0"));
        assert!(output.contains("s0 --> s1"));
        assert!(output.contains("s1 --> [*]"));
    }

    #[test]
    fn test_escape_mermaid_label() {
        assert_eq!(escape_mermaid_label("a|b"), "a\\|b");
        assert_eq!(escape_mermaid_label("<foo>"), "&lt;foo&gt;");
        assert_eq!(escape_mermaid_label("[test]"), "\\[test\\]");
    }
}
