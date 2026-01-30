//! Core Telltale library for session-typed communication.
//!
//! This crate provides session types (Send, Receive, Select, Branch, End) and
//! channel abstractions for safe multiparty communication.
//!
//! # Modules
//!
//! - [`types`] - Core session type definitions (GlobalType, LocalTypeR, Label)
//! - [`channel`] - Channel abstractions for communication
//!
//! # Feature Flags
//!
//! ## Core Features
//!
//! | Feature | Description |
//! |---------|-------------|
//! | `serialize` | Enable serialization support for session types |
//! | `test-utils` | Testing utilities (random generation, etc.) |
//! | `wasm` | WebAssembly support |
//!
//! ## Theory Features
//!
//! | Feature | Description |
//! |---------|-------------|
//! | `theory` | Session type algorithms (projection, merge, duality, etc.) |
//! | `theory-async-subtyping` | POPL 2021 asynchronous subtyping algorithm |
//! | `theory-bounded` | Bounded recursion strategies |
//!
//! ## Meta Features
//!
//! | Feature | Description |
//! |---------|-------------|
//! | `full` | Enable all optional features |

/// Channel abstractions for asynchronous communication.
pub mod channel;

// Re-export core types (always available)
pub use telltale_types as types;
pub use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort};

// Re-export optional crates
#[cfg(feature = "theory")]
pub use telltale_theory as theory;

pub use telltale_macros::{session, Message, Role, Roles};

/// Prelude module for convenient imports.
pub mod prelude {
    pub use super::{session, try_session};
    pub use super::{
        Branch, Choice, Choices, End, FromState, IntoSession, Message, Receive, ReceiveError, Role,
        Route, Select, Send, Session, SessionError,
    };
    pub use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort};
}

use futures::{FutureExt, Sink, SinkExt, Stream, StreamExt};
use std::{
    any::Any,
    convert::Infallible,
    future::Future,
    marker::{self, PhantomData},
};
use thiserror::Error;

/// Trait for types that can be sealed to prevent further use
pub trait Sealable {
    /// Seal this channel, preventing further operations
    fn seal(&mut self);

    /// Check if this channel is sealed
    fn is_sealed(&self) -> bool;
}

/// Error that can occur during a session send operation.
#[derive(Debug, Error)]
pub enum SessionError<E> {
    /// The session was used after being sealed.
    #[error("session was used after being sealed")]
    Sealed,
    /// An error from the underlying channel.
    #[error(transparent)]
    Channel(E),
}

/// Error type for send operations, specialized to the channel's error type.
pub type SendError<Q, R> =
    SessionError<<<Q as Route<R>>::Route as Sink<<Q as Role>::Message>>::Error>;

/// Error that can occur during a session receive operation.
#[derive(Debug, Error)]
pub enum ReceiveError {
    /// The receiver stream is empty (no messages available).
    #[error("receiver stream is empty")]
    EmptyStream,
    /// Received a message with an unexpected type.
    #[error("received message with an unexpected type")]
    UnexpectedType,
    /// The session was used after being sealed.
    #[error("session was used after being sealed")]
    Sealed,
}

/// This trait represents a message to be exchanged between two participants.
/// The generic type L is the type of the label (i.e. the content of the
/// message).
pub trait Message<L>: Sized {
    /// Creates a message from a label.
    fn upcast(label: L) -> Self;

    /// Tries to get the label contained in the `Message`. This might fail,
    /// typically if we are trying to get a label of the wrong type. In case of
    /// failure, the result contains `self`, hence the message is not lost.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the message does not contain a label of type `L`.
    fn downcast(self) -> Result<L, Self>;
}

impl<L: 'static> Message<L> for Box<dyn Any> {
    fn upcast(label: L) -> Self {
        Box::new(label)
    }

    fn downcast(self) -> Result<L, Self> {
        self.downcast().map(|label| *label)
    }
}

impl<L: marker::Send + 'static> Message<L> for Box<dyn Any + marker::Send> {
    fn upcast(label: L) -> Self {
        Box::new(label)
    }

    fn downcast(self) -> Result<L, Self> {
        self.downcast().map(|label| *label)
    }
}

impl<L: marker::Send + Sync + 'static> Message<L> for Box<dyn Any + marker::Send + Sync> {
    fn upcast(label: L) -> Self {
        Box::new(label)
    }

    fn downcast(self) -> Result<L, Self> {
        self.downcast().map(|label| *label)
    }
}

/// A participant in a session-typed protocol.
///
/// Roles define the message type and provide routing to other participants.
pub trait Role {
    /// The message type exchanged by this role.
    type Message;

    /// Seal all routes for this role, preventing further communication.
    fn seal(&mut self);

    /// Check if this role has been sealed.
    fn is_sealed(&self) -> bool;
}

/// Provides a route to another role for communication.
///
/// A role implements `Route<R>` for each peer role R it can communicate with.
pub trait Route<R>: Role + Sized {
    /// The channel type used to communicate with role R.
    type Route;

    /// Get a mutable reference to the route for sending/receiving messages.
    fn route(&mut self) -> &mut Self::Route;
}

/// This structure is mainly a placeholder for a `Role` and for types.
/// Typically, each each state (in the sense of automata state) of the protocol,
/// e.g. a `Send`, a `Receive`, etc, contains a `State`, as well as some type
/// bounds. When an action is taken (e.g. when `send` is called on a `Send`),
/// the `Send` will take it state and convert it into the continuation.
pub struct State<'r, R: Role> {
    role: &'r mut R,
}

impl<'r, R: Role> State<'r, R> {
    #[inline]
    fn new(role: &'r mut R) -> Self {
        Self { role }
    }
}

/// Trait for session types that can be constructed from a state.
///
/// All session types (Send, Receive, Select, Branch, End) implement this.
pub trait FromState<'r> {
    /// The role type this session state is for.
    type Role: Role;

    /// Construct this session state from the given state.
    fn from_state(state: State<'r, Self::Role>) -> Self;
}

/// Marker trait for session types in a protocol.
pub trait Session<'r>: FromState<'r> + private::Session {}

/// Trait for types that can be converted into a session.
pub trait IntoSession<'r>: FromState<'r> {
    /// The session type to convert into.
    type Session: Session<'r, Role = Self::Role>;

    /// Convert this value into a session.
    fn into_session(self) -> Self::Session;
}

/// This structure represents a terminated protocol.
pub struct End<'r, R: Role> {
    state: State<'r, R>,
}

impl<'r, R: Role> FromState<'r> for End<'r, R> {
    type Role = R;

    #[inline]
    fn from_state(state: State<'r, Self::Role>) -> Self {
        Self { state }
    }
}

impl<R: Role> End<'_, R> {
    /// Consume the End state and seal the role
    pub fn seal(self) {
        self.state.role.seal();
    }
}

impl<R: Role> Drop for End<'_, R> {
    fn drop(&mut self) {
        // Seal the role when End is dropped
        self.state.role.seal();
    }
}

impl<R: Role> private::Session for End<'_, R> {}

impl<'r, R: Role> Session<'r> for End<'r, R> {}

/// This structure represents a protocol which next action is to send.
pub struct Send<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> {
    state: State<'q, Q>,
    phantom: PhantomData<(R, L, S)>,
}

impl<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> FromState<'q> for Send<'q, Q, R, L, S> {
    type Role = Q;

    #[inline]
    fn from_state(state: State<'q, Self::Role>) -> Self {
        Self {
            state,
            phantom: PhantomData,
        }
    }
}

impl<'q, Q: Route<R>, R, L, S: FromState<'q, Role = Q>> Send<'q, Q, R, L, S>
where
    Q::Message: Message<L>,
    Q::Route: Sink<Q::Message> + Unpin,
{
    /// Sends a message to the peer role.
    ///
    /// # Errors
    ///
    /// Returns `Err(SessionError::Sealed)` if the session has been sealed.
    /// Returns `Err(SessionError::Channel(_))` if the underlying channel fails.
    #[inline]
    pub async fn send(self, label: L) -> Result<S, SendError<Q, R>> {
        if self.state.role.is_sealed() {
            return Err(SessionError::Sealed);
        }
        self.state
            .role
            .route()
            .send(Message::upcast(label))
            .await
            .map_err(SessionError::Channel)?;
        Ok(FromState::from_state(self.state))
    }
}

impl<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> private::Session for Send<'q, Q, R, L, S> {}

impl<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> Session<'q> for Send<'q, Q, R, L, S> {}

/// This structure represents a protocol which next action is to receive .
pub struct Receive<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> {
    state: State<'q, Q>,
    phantom: PhantomData<(R, L, S)>,
}

impl<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> FromState<'q> for Receive<'q, Q, R, L, S> {
    type Role = Q;

    #[inline]
    fn from_state(state: State<'q, Self::Role>) -> Self {
        Self {
            state,
            phantom: PhantomData,
        }
    }
}

impl<'q, Q: Route<R>, R, L, S: FromState<'q, Role = Q>> Receive<'q, Q, R, L, S>
where
    Q::Message: Message<L>,
    Q::Route: Stream<Item = Q::Message> + Unpin,
{
    /// Receives a message from the peer role.
    ///
    /// # Errors
    ///
    /// Returns `Err(ReceiveError::Sealed)` if the session has been sealed.
    /// Returns `Err(ReceiveError::EmptyStream)` if the channel has no messages.
    /// Returns `Err(ReceiveError::UnexpectedType)` if the message type is wrong.
    #[inline]
    pub async fn receive(self) -> Result<(L, S), ReceiveError> {
        if self.state.role.is_sealed() {
            return Err(ReceiveError::Sealed);
        }
        let message = self.state.role.route().next().await;
        let message = message.ok_or(ReceiveError::EmptyStream)?;
        let label = message.downcast().or(Err(ReceiveError::UnexpectedType))?;
        Ok((label, FromState::from_state(self.state)))
    }
}

impl<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> private::Session for Receive<'q, Q, R, L, S> {}

impl<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> Session<'q> for Receive<'q, Q, R, L, S> {}

/// Maps a choice label to its continuation session type.
pub trait Choice<'r, L> {
    /// The session type to continue with after selecting this label.
    type Session: FromState<'r>;
}

/// A protocol state where this role selects one of several branches.
///
/// The choice is sent to role R, and C determines the continuation for each label.
pub struct Select<'q, Q: Role, R, C> {
    state: State<'q, Q>,
    phantom: PhantomData<(R, C)>,
}

impl<'q, Q: Role, R, C> FromState<'q> for Select<'q, Q, R, C> {
    type Role = Q;

    #[inline]
    fn from_state(state: State<'q, Self::Role>) -> Self {
        Self {
            state,
            phantom: PhantomData,
        }
    }
}

impl<'q, Q: Route<R>, R, C> Select<'q, Q, R, C>
where
    Q::Route: Sink<Q::Message> + Unpin,
{
    /// Selects a branch to take in a choice, sending the label to the peer.
    ///
    /// # Errors
    ///
    /// Returns `Err(SessionError::Sealed)` if the session has been sealed.
    /// Returns `Err(SessionError::Channel(_))` if the underlying channel fails.
    #[inline]
    pub async fn select<L>(self, label: L) -> Result<<C as Choice<'q, L>>::Session, SendError<Q, R>>
    where
        Q::Message: Message<L>,
        C: Choice<'q, L>,
        C::Session: FromState<'q, Role = Q>,
    {
        if self.state.role.is_sealed() {
            return Err(SessionError::Sealed);
        }
        self.state
            .role
            .route()
            .send(Message::upcast(label))
            .await
            .map_err(SessionError::Channel)?;
        Ok(FromState::from_state(self.state))
    }
}

impl<Q: Role, R, C> private::Session for Select<'_, Q, R, C> {}

impl<'q, Q: Role, R, C> Session<'q> for Select<'q, Q, R, C> {}

/// Trait for an enum of possible branch choices.
///
/// Implemented by generated choice enums to dispatch incoming messages.
pub trait Choices<'r>: Sized {
    /// The role type this choice set is for.
    type Role: Role;

    /// Attempts to downcast a message into one of the available choices.
    ///
    /// # Errors
    ///
    /// Returns `Err(message)` if the message does not match any choice variant.
    fn downcast(
        state: State<'r, Self::Role>,
        message: <Self::Role as Role>::Message,
    ) -> Result<Self, <Self::Role as Role>::Message>;
}

/// A protocol state where this role receives one of several branch choices.
///
/// The choice is received from role R, and C is the enum of possible continuations.
pub struct Branch<'q, Q: Role, R, C> {
    state: State<'q, Q>,
    phantom: PhantomData<(R, C)>,
}

impl<'q, Q: Role, R, C> FromState<'q> for Branch<'q, Q, R, C> {
    type Role = Q;

    #[inline]
    fn from_state(state: State<'q, Self::Role>) -> Self {
        Self {
            state,
            phantom: PhantomData,
        }
    }
}

impl<'q, Q: Route<R>, R, C: Choices<'q, Role = Q>> Branch<'q, Q, R, C>
where
    Q::Route: Stream<Item = Q::Message> + Unpin,
{
    /// Waits for a message and branches based on which choice is received.
    ///
    /// # Errors
    ///
    /// Returns `Err(ReceiveError::Sealed)` if the session has been sealed.
    /// Returns `Err(ReceiveError::EmptyStream)` if the channel has no messages.
    /// Returns `Err(ReceiveError::UnexpectedType)` if the message type is wrong.
    #[inline]
    pub async fn branch(self) -> Result<C, ReceiveError> {
        if self.state.role.is_sealed() {
            return Err(ReceiveError::Sealed);
        }
        let message = self.state.role.route().next().await;
        let message = message.ok_or(ReceiveError::EmptyStream)?;
        let choice = C::downcast(self.state, message);
        choice.or(Err(ReceiveError::UnexpectedType))
    }
}

impl<Q: Role, R, C> private::Session for Branch<'_, Q, R, C> {}

impl<'q, Q: Role, R, C> Session<'q> for Branch<'q, Q, R, C> {}

/// Guard that ensures proper session cleanup and detects protocol violations
struct SessionGuard {
    completed: bool,
}

impl SessionGuard {
    fn new() -> Self {
        Self { completed: false }
    }

    fn mark_completed(&mut self) {
        self.completed = true;
    }
}

impl Drop for SessionGuard {
    fn drop(&mut self) {
        if !self.completed {
            // In debug mode, panic if the session was not properly completed
            #[cfg(debug_assertions)]
            {
                assert!(
                    std::thread::panicking(),
                    "Session dropped without completing! This indicates a protocol violation."
                );
            }
        }
    }
}

/// Run a session-typed protocol that cannot fail.
///
/// This is a convenience wrapper around [`try_session`] for infallible protocols.
#[inline]
pub async fn session<'r, R: Role, S: FromState<'r, Role = R>, T, F>(
    role: &'r mut R,
    f: impl FnOnce(S) -> F,
) -> T
where
    F: Future<Output = (T, End<'r, R>)>,
{
    let output = try_session(role, |s| f(s).map(Ok)).await;
    output.unwrap_or_else(|infallible: Infallible| match infallible {})
}

/// Runs a session that may fail, returning a result.
///
/// # Errors
///
/// Returns the error from the session function `f` if it fails.
#[inline]
pub async fn try_session<'r, R: Role, S: FromState<'r, Role = R>, T, E, F>(
    role: &'r mut R,
    f: impl FnOnce(S) -> F,
) -> Result<T, E>
where
    F: Future<Output = Result<(T, End<'r, R>), E>>,
{
    let mut guard = SessionGuard::new();
    let session = FromState::from_state(State::new(role));
    let result = f(session).await;

    if result.is_ok() {
        guard.mark_completed();
    }

    // End will seal the role when dropped
    result.map(|(output, _)| output)
}

mod private {
    pub trait Session {}
}

#[cfg(test)]
mod channel_test;
