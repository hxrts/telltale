// Core Rumpsteak library for session-typed communication
//
// Provides session types (Send, Receive, Select, Branch, End) and channel abstractions.

pub mod channel;
pub mod serialize;

pub use rumpsteak_aura_macros::{session, Message, Role, Roles};

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

#[derive(Debug, Error)]
pub enum SessionError<E> {
    #[error("session was used after being sealed")]
    Sealed,
    #[error(transparent)]
    Channel(E),
}

pub type SendError<Q, R> =
    SessionError<<<Q as Route<R>>::Route as Sink<<Q as Role>::Message>>::Error>;

#[derive(Debug, Error)]
pub enum ReceiveError {
    #[error("receiver stream is empty")]
    EmptyStream,
    #[error("received message with an unexpected type")]
    UnexpectedType,
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

pub trait Role {
    type Message;

    /// Seal all routes for this role, preventing further communication
    fn seal(&mut self);

    /// Check if this role has been sealed
    fn is_sealed(&self) -> bool;
}

pub trait Route<R>: Role + Sized {
    type Route;

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

pub trait FromState<'r> {
    type Role: Role;

    fn from_state(state: State<'r, Self::Role>) -> Self;
}

pub trait Session<'r>: FromState<'r> + private::Session {}

pub trait IntoSession<'r>: FromState<'r> {
    type Session: Session<'r, Role = Self::Role>;

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

pub trait Choice<'r, L> {
    type Session: FromState<'r>;
}

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

pub trait Choices<'r>: Sized {
    type Role: Role;

    fn downcast(
        state: State<'r, Self::Role>,
        message: <Self::Role as Role>::Message,
    ) -> Result<Self, <Self::Role as Role>::Message>;
}

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
                assert!(std::thread::panicking(), 
                        "Session dropped without completing! This indicates a protocol violation."
                    );
            }
        }
    }
}

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
