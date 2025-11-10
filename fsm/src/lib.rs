//! Finite State Machine (FSM) support for session types.
//!
//! This crate provides finite state machine representations for session types,
//! enabling static analysis and verification of communication protocols. It includes
//! support for DOT parsing, local type representations, subtyping verification,
//! and Petrify output format.
//!
//! # Main Components
//!
//! - [`Fsm`] - Core FSM representation with states and transitions
//! - [`Local`] - Local type representation (textual session types)
//! - [`Dot`] - DOT format export for visualization
//! - [`Petrify`] - Petrify format export for Petri net tools
//! - [`subtype`] - Asynchronous subtyping verification
//!
//! # Example
//!
//! ```rust
//! use rumpsteak_aura_fsm::{Fsm, Action, Message, Transition};
//!
//! let mut fsm: Fsm<&str, &str, ()> = Fsm::new("Client");
//! let s0 = fsm.add_state();
//! let s1 = fsm.add_state();
//!
//! let transition = Transition::new(
//!     "Server",
//!     Action::Output,
//!     Message::from_label("Hello")
//! );
//! fsm.add_transition(s0, s1, transition).unwrap();
//! ```

pub mod dot;
pub mod local;
pub mod petrify;
pub mod subtype;

pub use self::{dot::Dot, local::Local, petrify::Petrify};

use petgraph::{graph::NodeIndex, visit::EdgeRef, Graph};
use std::{
    collections::HashMap,
    fmt::{self, Debug, Display, Formatter},
    hash::Hash,
};
use thiserror::Error;

/// Nil type representing the absence of a role in binary FSMs.
///
/// Used when converting multi-role FSMs to binary (two-party) FSMs
/// where only one peer role needs to be tracked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Nil;

impl Display for Nil {
    fn fmt(&self, _: &mut Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

/// Communication action performed by a role.
///
/// Represents whether a role is sending (Output) or receiving (Input) a message.
/// These actions are dual to each other: if one role outputs, the other must input.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Action {
    /// Receiving a message (represented as `?` in DOT format)
    Input,
    /// Sending a message (represented as `!` in DOT format)
    Output,
}

impl Action {
    /// Returns the dual action.
    ///
    /// The dual of Input is Output and vice versa.
    fn dual(self) -> Self {
        match self {
            Self::Input => Self::Output,
            Self::Output => Self::Input,
        }
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input => write!(f, "?"),
            Self::Output => write!(f, "!"),
        }
    }
}

/// Operator associativity for expression parsing.
///
/// Determines the order in which operators of the same precedence are evaluated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Associativity {
    /// Left-to-right associativity (e.g., `a + b + c` = `(a + b) + c`)
    Left,
    /// Right-to-left associativity (e.g., `a = b = c` = `a = (b = c)`)
    Right,
}

/// Trait for operators in expressions.
///
/// Defines precedence and associativity for operator parsing in refinement expressions.
pub trait Operator {
    /// Returns the precedence level of this operator.
    ///
    /// Lower numbers bind more tightly (higher precedence).
    fn precedence(&self) -> usize;

    /// Returns the associativity of this operator.
    fn associativity(&self) -> Associativity;
}

/// Unary operators for refinement expressions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    /// Logical negation (`!`)
    Not,
    /// Arithmetic negation (`-`)
    Minus,
}

impl Operator for UnaryOp {
    fn associativity(&self) -> Associativity {
        Associativity::Right
    }

    fn precedence(&self) -> usize {
        2
    }
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Not => write!(f, "!"),
            Self::Minus => write!(f, "-"),
        }
    }
}

/// Binary operators for refinement expressions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    /// Logical AND (`&&`)
    LAnd,
    /// Logical OR (`||`)
    LOr,
    /// Equality (`=`)
    Equal,
    /// Inequality (`<>`)
    NotEqual,
    /// Less than (`<`)
    Less,
    /// Greater than (`>`)
    Greater,
    /// Less than or equal (`<=`)
    LessEqual,
    /// Greater than or equal (`>=`)
    GreaterEqual,
    /// Addition (`+`)
    Add,
    /// Subtraction (`-`)
    Subtract,
    /// Multiplication (`*`)
    Multiply,
    /// Division (`/`)
    Divide,
    /// Bitwise AND (`&`)
    And,
    /// Bitwise XOR (`^`)
    Xor,
    /// Bitwise OR (`|`)
    Or,
}

impl Operator for BinaryOp {
    fn associativity(&self) -> Associativity {
        match self {
            Self::LAnd | Self::LOr | Self::Equal | Self::NotEqual | Self::Less | Self::Greater 
            | Self::LessEqual | Self::GreaterEqual | Self::Add | Self::Subtract | Self::Multiply 
            | Self::Divide | Self::And | Self::Xor | Self::Or => Associativity::Left,
        }
    }

    fn precedence(&self) -> usize {
        match self {
            Self::LAnd => 11,
            Self::LOr => 12,
            Self::Equal | Self::NotEqual => 7,
            Self::Less | Self::Greater | Self::LessEqual | Self::GreaterEqual => 6,
            Self::Add | Self::Subtract => 4,
            Self::Multiply | Self::Divide => 3,
            Self::And => 8,
            Self::Xor => 9,
            Self::Or => 10,
        }
    }
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::LAnd => write!(f, "&&"),
            Self::LOr => write!(f, "||"),
            Self::Equal => write!(f, "="),
            Self::NotEqual => write!(f, "<>"),
            Self::Less => write!(f, "<"),
            Self::Greater => write!(f, ">"),
            Self::LessEqual => write!(f, "<="),
            Self::GreaterEqual => write!(f, ">="),
            Self::Add => write!(f, "+"),
            Self::Subtract => write!(f, "-"),
            Self::Multiply => write!(f, "*"),
            Self::Divide => write!(f, "/"),
            Self::And => write!(f, "&"),
            Self::Xor => write!(f, "^"),
            Self::Or => write!(f, "|"),
        }
    }
}

/// Refinement expression for message parameters.
///
/// Expressions are used to specify constraints on message parameters in refined session types.
/// They support variables, constants, and unary/binary operations.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expression<N> {
    /// Variable reference
    Name(N),
    /// Boolean constant
    Boolean(bool),
    /// Numeric constant
    Number(usize),
    /// Unary operation
    Unary(UnaryOp, Box<Self>),
    /// Binary operation
    Binary(BinaryOp, Box<Self>, Box<Self>),
}

impl<N: Display> Expression<N> {
    fn fmt_bracketed(
        &self,
        f: &mut Formatter<'_>,
        associativity: Associativity,
        precedence: usize,
        op: &impl Operator,
        fmt: impl FnOnce(&mut Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        if op.precedence() > precedence
            || (op.precedence() == precedence && op.associativity() == associativity)
        {
            write!(f, "(")?;
            fmt(f)?;
            return write!(f, ")");
        }

        fmt(f)
    }

    fn fmt_inner(
        &self,
        f: &mut Formatter<'_>,
        associativity: Associativity,
        precedence: usize,
    ) -> fmt::Result {
        match self {
            Self::Name(name) => write!(f, "{name}"),
            Self::Boolean(boolean) => write!(f, "{boolean}"),
            Self::Number(number) => write!(f, "{number}"),
            Self::Unary(op, expression) => {
                self.fmt_bracketed(f, associativity, precedence, op, |f| {
                    write!(f, "{op}")?;
                    expression.fmt_inner(f, Associativity::Left, op.precedence())
                })
            }
            Self::Binary(op, left, right) => {
                self.fmt_bracketed(f, associativity, precedence, op, |f| {
                    left.fmt_inner(f, Associativity::Right, op.precedence())?;
                    write!(f, " {op} ")?;
                    right.fmt_inner(f, Associativity::Left, op.precedence())
                })
            }
        }
    }
}

impl<N: Display> Display for Expression<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.fmt_inner(f, Associativity::Left, usize::MAX)
    }
}

/// Named parameter with optional refinement type.
///
/// Represents a parameter with a name, type (sort), and optional refinement expression.
/// Example: `x: Int{x > 0}` where `x` is the name, `Int` is the sort, and `x > 0` is the refinement.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NamedParameter<N, E> {
    name: N,
    sort: N,
    refinement: Option<E>,
}

impl<N, E> NamedParameter<N, E> {
    /// Creates a new named parameter.
    pub fn new(name: N, sort: N, refinement: Option<E>) -> Self {
        Self {
            name,
            sort,
            refinement,
        }
    }
}

impl<N: Display, E: Display> Display for NamedParameter<N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.sort)?;
        if let Some(refinement) = &self.refinement {
            write!(f, "{{{refinement}}}")?;
        }

        Ok(())
    }
}

/// Message parameters, either unnamed or named with refinements.
///
/// Parameters can be either a simple list of types (unnamed) or
/// a list of named parameters with optional refinement types (named).
/// Mixing unnamed and named parameters is not allowed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Parameters<N, E> {
    /// Unnamed parameters (just types)
    Unnamed(Vec<N>),
    /// Named parameters with optional refinements
    Named(Vec<NamedParameter<N, E>>),
}

impl<N, E> Default for Parameters<N, E> {
    fn default() -> Self {
        Self::Unnamed(Vec::new())
    }
}

impl<N, E> Parameters<N, E> {
    /// Returns true if there are no parameters.
    #[must_use] 
    pub fn is_empty(&self) -> bool {
        match self {
            Parameters::Unnamed(parameters) => parameters.is_empty(),
            Parameters::Named(parameters) => parameters.is_empty(),
        }
    }
}

impl<N: Display, E: Display> Display for Parameters<N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        fn fmt<T: Display>(values: &[T], f: &mut Formatter<'_>) -> fmt::Result {
            let mut values = values.iter();
            if let Some(value) = values.next() {
                write!(f, "{value}")?;
                for value in values {
                    write!(f, ", {value}")?;
                }
            }

            Ok(())
        }

        match self {
            Self::Unnamed(params) => fmt(params, f),
            Self::Named(params) => fmt(params, f),
        }
    }
}

/// Message with label, parameters, and assignments.
///
/// Represents a message in a session type protocol with its label, optional parameters,
/// and optional variable assignments for refinements.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Message<N, E> {
    label: N,
    parameters: Parameters<N, E>,
    assignments: Vec<(N, E)>,
}

impl<N, E> Message<N, E> {
    /// Creates a new message with label, parameters, and assignments.
    pub fn new(label: N, parameters: Parameters<N, E>, assignments: Vec<(N, E)>) -> Self {
        Self {
            label,
            parameters,
            assignments,
        }
    }

    /// Creates a message with just a label (no parameters or assignments).
    pub fn from_label(label: N) -> Self {
        Self::new(label, Default::default(), Default::default())
    }
}

impl<N: Display, E: Display> Display for Message<N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.label)?;
        if !self.parameters.is_empty() {
            write!(f, "({})", self.parameters)?;
        }

        let mut assignments = self.assignments.iter();
        if let Some((name, refinement)) = assignments.next() {
            write!(f, "[{name}: {refinement}")?;
            for (name, refinement) in assignments {
                write!(f, ", {name}: {refinement}")?;
            }

            write!(f, "]")?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
struct Choices<R> {
    role: R,
    action: Action,
}

#[derive(Clone, Debug)]
enum State<R> {
    Choices(Choices<R>),
    End,
}

/// Index of a state in the FSM graph.
///
/// Wraps petgraph's `NodeIndex` to provide a type-safe handle to FSM states.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct StateIndex(NodeIndex);

impl StateIndex {
    /// Returns the numeric index of this state.
    pub(crate) fn index(self) -> usize {
        self.0.index()
    }
}

/// FSM transition representing a communication action.
///
/// A transition includes:
/// - The peer role being communicated with
/// - The action (Input or Output)
/// - The message being sent/received
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Transition<R, N, E> {
    /// The peer role
    pub role: R,
    /// The communication action
    pub action: Action,
    /// The message
    pub message: Message<N, E>,
}

impl<R, N, E> Transition<R, N, E> {
    /// Creates a new transition.
    pub fn new(role: R, action: Action, message: Message<N, E>) -> Self {
        Self {
            role,
            action,
            message,
        }
    }

    /// Returns a borrowed reference to this transition.
    pub fn as_ref(&self) -> TransitionRef<'_, R, N, E> {
        TransitionRef::new(&self.role, self.action, &self.message)
    }
}

impl<R: Display, N: Display, E: Display> Display for Transition<R, N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.role, self.action, self.message)
    }
}

/// Borrowed reference to a transition.
///
/// Like [`Transition`], but holds borrowed references instead of owned values.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct TransitionRef<'a, R, N, E> {
    /// Reference to the peer role
    pub role: &'a R,
    /// The communication action
    pub action: Action,
    /// Reference to the message
    pub message: &'a Message<N, E>,
}

impl<'a, R, N, E> TransitionRef<'a, R, N, E> {
    /// Creates a new transition reference.
    pub fn new(role: &'a R, action: Action, message: &'a Message<N, E>) -> Self {
        Self {
            role,
            action,
            message,
        }
    }
}

impl<R, N, E> Clone for TransitionRef<'_, R, N, E> {
    fn clone(&self) -> Self {
        Self::new(self.role, self.action, self.message)
    }
}

impl<R: Clone, N: Clone, E: Clone> TransitionRef<'_, R, N, E> {
    /// Converts this transition reference to an owned transition.
    #[must_use] 
    pub fn to_owned(&self) -> Transition<R, N, E> {
        Transition::new(self.role.clone(), self.action, self.message.clone())
    }
}

impl<R: Display, N: Display, E: Display> Display for TransitionRef<'_, R, N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.role, self.action, self.message)
    }
}

/// Errors that can occur when adding transitions to an FSM.
#[derive(Debug, Error)]
pub enum AddTransitionError {
    /// Attempted to add a transition where the FSM role communicates with itself
    #[error("cannot perform self-communication")]
    SelfCommunication,
    /// Attempted to add transitions with different peer roles from the same state
    #[error("cannot communicate with different roles from the same state")]
    MultipleRoles,
    /// Attempted to add both send and receive transitions from the same state
    #[error("cannot both send and receive from the same state")]
    MultipleActions,
}

/// Finite state machine representing a local session type.
///
/// An FSM consists of states and transitions between them. Each transition
/// represents a communication action (send or receive) with a peer role.
/// The FSM represents the protocol from the perspective of a single role.
///
/// # Type Parameters
///
/// - `R` - Role type (e.g., `String`, `&str`)
/// - `N` - Name type for message labels and parameters (e.g., `String`)
/// - `E` - Expression type for refinements (e.g., `Expression<String>` or `Infallible`)
#[derive(Clone, Debug)]
pub struct Fsm<R, N, E> {
    role: R,
    graph: Graph<State<R>, Message<N, E>>,
}

impl<R, N, E> Fsm<R, N, E> {
    /// Creates a new FSM for the given role with no states or transitions.
    pub fn new(role: R) -> Self {
        let graph = Graph::new();
        Self { role, graph }
    }

    /// Returns the role this FSM represents.
    pub fn role(&self) -> &R {
        &self.role
    }

    /// Returns the size of this FSM as (number of states, number of transitions).
    pub fn size(&self) -> (usize, usize) {
        (self.graph.node_count(), self.graph.edge_count())
    }

    /// Returns an iterator over all state indices in this FSM.
    pub fn states(&self) -> impl Iterator<Item = StateIndex> {
        self.graph.node_indices().map(StateIndex)
    }

    /// Returns an iterator over all transitions in this FSM.
    ///
    /// Each item is a tuple of (source state, target state, transition).
    pub fn transitions(
        &self,
    ) -> impl Iterator<Item = (StateIndex, StateIndex, TransitionRef<'_, R, N, E>)> {
        self.graph.edge_references().map(move |edge| {
            let (source, target) = (StateIndex(edge.source()), StateIndex(edge.target()));
            match &self.graph[edge.source()] {
                State::Choices(choices) => {
                    let transition =
                        TransitionRef::new(&choices.role, choices.action, edge.weight());
                    (source, target, transition)
                }
                State::End => unreachable!(),
            }
        })
    }

    /// Returns an iterator over transitions from a specific state.
    ///
    /// Each item is a tuple of (target state, transition).
    pub fn transitions_from(
        &self,
        StateIndex(index): StateIndex,
    ) -> impl Iterator<Item = (StateIndex, TransitionRef<'_, R, N, E>)> {
        self.graph
            .edges(index)
            .map(move |edge| match &self.graph[index] {
                State::Choices(choices) => {
                    let transition =
                        TransitionRef::new(&choices.role, choices.action, edge.weight());
                    (StateIndex(edge.target()), transition)
                }
                State::End => unreachable!(),
            })
    }

    /// Adds a new state to the FSM and returns its index.
    pub fn add_state(&mut self) -> StateIndex {
        StateIndex(self.graph.add_node(State::End))
    }

    /// Adds a transition between two states.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The transition represents self-communication
    /// - The source state already has transitions to different peer roles
    /// - The source state already has transitions with different actions (send vs receive)
    pub fn add_transition(
        &mut self,
        from: StateIndex,
        to: StateIndex,
        transition: Transition<R, N, E>,
    ) -> Result<(), AddTransitionError>
    where
        R: Eq,
    {
        if transition.role == self.role {
            return Err(AddTransitionError::SelfCommunication);
        }

        let choices = Choices {
            role: transition.role,
            action: transition.action,
        };

        let state = &mut self.graph[from.0];
        match state {
            State::End => *state = State::Choices(choices),
            State::Choices(expected) => {
                if choices.role != expected.role {
                    return Err(AddTransitionError::MultipleRoles);
                }

                if choices.action != expected.action {
                    return Err(AddTransitionError::MultipleActions);
                }
            }
        }

        self.graph.add_edge(from.0, to.0, transition.message);
        Ok(())
    }

    /// Converts this FSM to a binary (two-party) FSM.
    ///
    /// In a binary FSM, all transitions must be with the same peer role.
    /// The peer role information is erased and replaced with [`Nil`].
    ///
    /// # Panics
    ///
    /// Panics if transitions communicate with different peer roles.
    pub fn to_binary(&self) -> Fsm<Nil, N, E>
    where
        R: Debug + Eq,
        N: Clone,
        E: Clone,
    {
        let mut role = None;
        let graph = self.graph.map(
            |_, state| match state {
                State::Choices(choice) => {
                    match role {
                        Some(role) => assert_eq!(role, &choice.role),
                        None => role = Some(&choice.role),
                    }

                    State::Choices(Choices {
                        role: Nil,
                        action: choice.action,
                    })
                }
                State::End => State::End,
            },
            |_, edge| edge.clone(),
        );

        Fsm { role: Nil, graph }
    }

    /// Creates the dual FSM from the perspective of the peer role.
    ///
    /// The dual FSM has:
    /// - The peer role as its role
    /// - All actions flipped (Input ↔ Output)
    /// - The same structure otherwise
    ///
    /// # Panics
    ///
    /// Panics if any transition is not with the specified peer role.
    #[must_use]
    pub fn dual(&self, role: R) -> Self
    where
        R: Clone + Debug + Eq,
        N: Clone,
        E: Clone,
    {
        let graph = self.graph.map(
            |_, state| match state {
                State::Choices(choice) => {
                    assert_eq!(role, choice.role);
                    State::Choices(Choices {
                        role: self.role.clone(),
                        action: choice.action.dual(),
                    })
                }
                State::End => State::End,
            },
            |_, edge| edge.clone(),
        );

        Fsm { role, graph }
    }
}

/// Normalizer for converting FSMs to canonical form.
///
/// Replaces role and label names with numeric indices for comparison
/// and analysis. Useful for checking structural equivalence of FSMs.
pub struct Normalizer<'a, R, N> {
    roles: HashMap<&'a R, usize>,
    labels: HashMap<&'a N, usize>,
}

impl<R, N> Default for Normalizer<'_, R, N> {
    fn default() -> Self {
        Self {
            roles: Default::default(),
            labels: Default::default(),
        }
    }
}

impl<'a, R: Eq + Hash, N: Eq + Hash> Normalizer<'a, R, N> {
    fn role(roles: &mut HashMap<&'a R, usize>, role: &'a R) -> usize {
        let next_index = roles.len();
        *roles.entry(role).or_insert(next_index)
    }

    fn label(labels: &mut HashMap<&'a N, usize>, label: &'a N) -> usize {
        let next_index = labels.len();
        *labels.entry(label).or_insert(next_index)
    }

    /// Normalizes an FSM by replacing names with numeric indices.
    ///
    /// Role and label names are replaced with unique indices based on
    /// the order they are first encountered. This produces a canonical
    /// representation for structural comparison.
    pub fn normalize<E: Clone>(&mut self, input: &'a Fsm<R, N, E>) -> Fsm<usize, usize, E> {
        let (roles, labels) = (&mut self.roles, &mut self.labels);
        Fsm {
            role: Self::role(roles, &input.role),
            graph: input.graph.map(
                |_, state| match state {
                    State::End => State::End,
                    State::Choices(choices) => State::Choices(Choices {
                        role: Self::role(roles, &choices.role),
                        action: choices.action,
                    }),
                },
                |_, message| Message::from_label(Self::label(labels, &message.label)),
            ),
        }
    }
}
