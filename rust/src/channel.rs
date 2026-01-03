// Channel abstractions for session-typed communication
//
// Provides bidirectional channels with Sink and Stream implementations,
// and channel pairing utilities for session types.

use crate::Sealable;
use futures::{channel::mpsc, Sink, Stream};
use std::{
    pin::Pin,
    task::{Context, Poll},
};

/// Trait for types that can be paired with a dual type.
///
/// Used to create matched channel endpoints (e.g., sender/receiver pairs).
pub trait Pair<P: Pair<Self>>: Sized {
    /// Create a new pair of dual endpoints.
    fn pair() -> (Self, P);
}

/// An empty channel placeholder representing no communication.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Nil;

impl Pair<Nil> for Nil {
    #[inline]
    fn pair() -> (Nil, Nil) {
        (Nil, Nil)
    }
}

impl Sealable for Nil {
    fn seal(&mut self) {
        // Nil has no channels to seal
    }

    fn is_sealed(&self) -> bool {
        // Nil is never sealed (or always sealed - doesn't matter)
        false
    }
}

impl<T> Pair<mpsc::UnboundedReceiver<T>> for mpsc::UnboundedSender<T> {
    fn pair() -> (Self, mpsc::UnboundedReceiver<T>) {
        mpsc::unbounded()
    }
}

impl<T> Pair<mpsc::UnboundedSender<T>> for mpsc::UnboundedReceiver<T> {
    fn pair() -> (Self, mpsc::UnboundedSender<T>) {
        let (sender, receiver) = Pair::pair();
        (receiver, sender)
    }
}

impl<T> Sealable for mpsc::UnboundedSender<T> {
    fn seal(&mut self) {
        // Close the sender
        self.close_channel();
    }

    fn is_sealed(&self) -> bool {
        // Check if the sender is closed
        self.is_closed()
    }
}

impl<T> Sealable for mpsc::UnboundedReceiver<T> {
    fn seal(&mut self) {
        // Close the receiver by dropping
        self.close();
    }

    fn is_sealed(&self) -> bool {
        // Receivers don't have a direct is_closed check
        // We'll consider them never sealed since they're passive
        false
    }
}

/// A bidirectional channel combining a sender and receiver.
///
/// Implements both `Sink` and `Stream` for full-duplex communication.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bidirectional<S, R> {
    sender: S,
    receiver: R,
    sealed: bool,
}

impl<S, R> Bidirectional<S, R> {
    /// Create a new bidirectional channel from a sender and receiver.
    pub fn new(sender: S, receiver: R) -> Self {
        Self {
            sender,
            receiver,
            sealed: false,
        }
    }
}

impl<S: Pair<R>, R: Pair<S>> Pair<Self> for Bidirectional<S, R> {
    fn pair() -> (Self, Self) {
        let (left_sender, right_receiver) = Pair::pair();
        let (right_sender, left_receiver) = Pair::pair();
        (
            Bidirectional::new(left_sender, left_receiver),
            Bidirectional::new(right_sender, right_receiver),
        )
    }
}

impl<S: Unpin, R: Unpin> Bidirectional<S, R> {
    fn sender(self: Pin<&mut Self>) -> Pin<&mut S> {
        Pin::new(&mut self.get_mut().sender)
    }

    fn receiver(self: Pin<&mut Self>) -> Pin<&mut R> {
        Pin::new(&mut self.get_mut().receiver)
    }
}

impl<T, S: Sink<T> + Unpin, R: Unpin> Sink<T> for Bidirectional<S, R> {
    type Error = S::Error;

    fn poll_ready(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        S::poll_ready(self.sender(), cx)
    }

    fn start_send(self: Pin<&mut Self>, item: T) -> Result<(), Self::Error> {
        S::start_send(self.sender(), item)
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        S::poll_flush(self.sender(), cx)
    }

    fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        S::poll_close(self.sender(), cx)
    }
}

impl<S: Unpin, R: Stream + Unpin> Stream for Bidirectional<S, R> {
    type Item = R::Item;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // Check sealed status before delegating to receiver
        if self.sealed {
            return Poll::Ready(None);
        }
        // Use the receiver() helper for consistent Pin projection
        R::poll_next(self.as_mut().receiver(), cx)
    }
}

impl<S, R> Sealable for Bidirectional<S, R> {
    fn seal(&mut self) {
        self.sealed = true;
    }

    fn is_sealed(&self) -> bool {
        self.sealed
    }
}
