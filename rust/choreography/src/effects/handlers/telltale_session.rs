use super::{ChoreoResult, ChoreographyError};
use futures::{channel::mpsc, future::BoxFuture, SinkExt, StreamExt};
use std::fmt::Debug;

/// Metadata describing the evolution of a session with a peer.
#[derive(Debug, Clone)]
pub struct SessionMetadata {
    /// Human-readable description of the last state/operation.
    pub state_description: String,
    /// Whether the session has reached its terminal state.
    pub is_complete: bool,
    /// Number of operations performed on this session.
    pub operation_count: usize,
}

impl Default for SessionMetadata {
    fn default() -> Self {
        Self {
            state_description: "Initial".to_string(),
            is_complete: false,
            operation_count: 0,
        }
    }
}

/// Result of executing a session operation.
#[derive(Debug)]
pub struct SessionUpdate<T> {
    pub output: T,
    pub description: Option<String>,
    pub is_complete: bool,
}

impl<T> SessionUpdate<T> {
    pub fn new(output: T) -> Self {
        Self {
            output,
            description: None,
            is_complete: false,
        }
    }

    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }

    pub fn mark_complete(mut self) -> Self {
        self.is_complete = true;
        self
    }
}

/// Dynamic session trait used by `TelltaleSession`.
pub trait SessionTypeDynamic: Send {
    /// Identify the underlying session for diagnostics.
    fn type_name(&self) -> &'static str;

    /// Send a serialized message.
    fn send(&mut self, _data: Vec<u8>) -> BoxFuture<'_, ChoreoResult<SessionUpdate<()>>> {
        unsupported("send", self.type_name())
    }

    /// Receive a serialized message.
    fn recv(&mut self) -> BoxFuture<'_, ChoreoResult<SessionUpdate<Vec<u8>>>> {
        unsupported("recv", self.type_name())
    }

    /// Make a choice/selection.
    fn choose(&mut self, _label: &str) -> BoxFuture<'_, ChoreoResult<SessionUpdate<()>>> {
        unsupported("choose", self.type_name())
    }

    /// Offer a branch selection.
    fn offer(&mut self) -> BoxFuture<'_, ChoreoResult<SessionUpdate<String>>> {
        unsupported("offer", self.type_name())
    }
}

fn unsupported<T>(
    operation: &'static str,
    name: &'static str,
) -> BoxFuture<'static, ChoreoResult<SessionUpdate<T>>> {
    Box::pin(async move {
        Err(ChoreographyError::ProtocolViolation(format!(
            "{name} does not support {operation} operations"
        )))
    })
}

/// Generic session backed by independent sink/stream pairs.
struct SinkStreamSession<S, R> {
    sender: S,
    receiver: R,
    label: &'static str,
}

impl<S, R> SinkStreamSession<S, R> {
    fn new(sender: S, receiver: R, label: &'static str) -> Self {
        Self {
            sender,
            receiver,
            label,
        }
    }
}

impl<S, R> SessionTypeDynamic for SinkStreamSession<S, R>
where
    S: futures::Sink<Vec<u8>> + Unpin + Send,
    S::Error: std::fmt::Display + Send + 'static,
    R: futures::Stream<Item = Vec<u8>> + Unpin + Send,
{
    fn type_name(&self) -> &'static str {
        self.label
    }

    fn send(&mut self, data: Vec<u8>) -> BoxFuture<'_, ChoreoResult<SessionUpdate<()>>> {
        let sender = &mut self.sender;
        Box::pin(async move {
            sender
                .send(data)
                .await
                .map_err(|e| ChoreographyError::ChannelSendFailed {
                    channel_type: "SinkStream",
                    reason: e.to_string(),
                })?;
            Ok(SessionUpdate::new(()).with_description("Send"))
        })
    }

    fn recv(&mut self) -> BoxFuture<'_, ChoreoResult<SessionUpdate<Vec<u8>>>> {
        let receiver = &mut self.receiver;
        Box::pin(async move {
            let bytes = receiver
                .next()
                .await
                .ok_or(ChoreographyError::ChannelClosed {
                    channel_type: "SinkStream",
                    operation: "receive",
                })?;
            Ok(SessionUpdate::new(bytes).with_description("Recv"))
        })
    }

    fn choose(&mut self, label: &str) -> BoxFuture<'_, ChoreoResult<SessionUpdate<()>>> {
        let sender = &mut self.sender;
        let data = label.to_string();
        Box::pin(async move {
            let bytes = bincode::serialize(&data).map_err(|e| {
                ChoreographyError::LabelSerializationFailed {
                    operation: "serialization",
                    reason: e.to_string(),
                }
            })?;
            sender
                .send(bytes)
                .await
                .map_err(|e| ChoreographyError::ChannelSendFailed {
                    channel_type: "SinkStream",
                    reason: e.to_string(),
                })?;
            Ok(SessionUpdate::new(()).with_description("Choose"))
        })
    }

    fn offer(&mut self) -> BoxFuture<'_, ChoreoResult<SessionUpdate<String>>> {
        let receiver = &mut self.receiver;
        Box::pin(async move {
            let bytes = receiver
                .next()
                .await
                .ok_or(ChoreographyError::ChannelClosed {
                    channel_type: "SinkStream",
                    operation: "offer",
                })?;
            let label: String = bincode::deserialize(&bytes).map_err(|e| {
                ChoreographyError::LabelSerializationFailed {
                    operation: "deserialization",
                    reason: e.to_string(),
                }
            })?;
            Ok(SessionUpdate::new(label).with_description("Offer"))
        })
    }
}

/// Wrapper around a dynamic session object.
pub struct TelltaleSession {
    inner: Box<dyn SessionTypeDynamic>,
}

impl Debug for TelltaleSession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TelltaleSession")
            .field("session", &self.type_name())
            .finish()
    }
}

impl TelltaleSession {
    #[must_use]
    pub fn new(inner: Box<dyn SessionTypeDynamic>) -> Self {
        Self { inner }
    }

    /// Build a session from independent sink/stream transports.
    pub fn from_sink_stream<S, R>(sender: S, receiver: R) -> Self
    where
        S: futures::Sink<Vec<u8>> + Unpin + Send + 'static,
        S::Error: std::fmt::Display + Send + 'static,
        R: futures::Stream<Item = Vec<u8>> + Unpin + Send + 'static,
    {
        let label = std::any::type_name::<S>();
        Self::new(Box::new(SinkStreamSession::new(sender, receiver, label)))
    }

    /// Build a connected pair of sessions over in-process async byte streams.
    #[must_use]
    pub fn pair() -> (Self, Self) {
        let (left_tx, left_rx) = mpsc::unbounded::<Vec<u8>>();
        let (right_tx, right_rx) = mpsc::unbounded::<Vec<u8>>();
        (
            Self::from_sink_stream(left_tx, right_rx),
            Self::from_sink_stream(right_tx, left_rx),
        )
    }

    #[must_use]
    pub fn type_name(&self) -> &'static str {
        self.inner.type_name()
    }

    pub async fn send(&mut self, data: Vec<u8>) -> ChoreoResult<SessionUpdate<()>> {
        self.inner.send(data).await
    }

    pub async fn recv(&mut self) -> ChoreoResult<SessionUpdate<Vec<u8>>> {
        self.inner.recv().await
    }

    pub async fn choose(&mut self, label: &str) -> ChoreoResult<SessionUpdate<()>> {
        self.inner.choose(label).await
    }

    pub async fn offer(&mut self) -> ChoreoResult<SessionUpdate<String>> {
        self.inner.offer().await
    }
}
