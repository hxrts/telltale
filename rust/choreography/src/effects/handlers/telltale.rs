// Telltale session-typed effect handler
//
// This handler provides a unified abstraction over bidirectional channels
// and dynamically dispatched session objects. Users can keep using the
// legacy SimpleChannel transport or register custom session interpreters
// through the TelltaleSession wrapper.
//
// Key pieces:
// - SimpleChannel: thin wrapper around telltale bidirectional channels.
// - SessionTypeDynamic: async trait (object safe via BoxFuture) that lets any
//   session state expose send/recv/choose/offer operations.
// - TelltaleSession: boxed dynamic session with metadata integration.
// - TelltaleEndpoint: tracks per-peer channels/sessions plus metadata.
// - TelltaleHandler: implements ChoreoHandler over either transport.

use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::{collections::HashMap, fmt::Debug, marker::PhantomData, time::Duration};

use crate::effects::{ChoreoHandler, ChoreoResult, ChoreographyError, LabelId, RoleId};
use telltale::{Message, Role};

#[path = "telltale_session.rs"]
mod session;
pub use session::{
    SessionMetadata, SessionTypeDynamic, SessionUpdate, SimpleChannel, TelltaleSession,
};

enum ChannelState {
    Simple(SimpleChannel),
    Session(TelltaleSession),
}

struct ChannelRecord {
    state: ChannelState,
    metadata: SessionMetadata,
}

/// Endpoint that manages per-peer channels/sessions plus metadata.
pub struct TelltaleEndpoint<R>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    local_role: R,
    channels: HashMap<R, ChannelRecord>,
}

impl<R> TelltaleEndpoint<R>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    pub fn new(local_role: R) -> Self {
        Self {
            local_role,
            channels: HashMap::new(),
        }
    }

    /// Register a legacy `SimpleChannel` for a peer.
    pub fn register_channel(&mut self, peer: R, channel: SimpleChannel) {
        tracing::debug!(?peer, "Registering SimpleChannel session");
        self.channels.insert(
            peer,
            ChannelRecord {
                state: ChannelState::Simple(channel),
                metadata: SessionMetadata::default(),
            },
        );
    }

    /// Register a dynamic session for a peer.
    pub fn register_session(&mut self, peer: R, session: TelltaleSession) {
        tracing::debug!(peer = ?peer, session = session.type_name(), "Registering dynamic session");
        self.channels.insert(
            peer,
            ChannelRecord {
                state: ChannelState::Session(session),
                metadata: SessionMetadata::default(),
            },
        );
    }

    fn take_record(&mut self, peer: &R) -> Option<ChannelRecord> {
        self.channels.remove(peer)
    }

    fn put_record(&mut self, peer: R, record: ChannelRecord) {
        self.channels.insert(peer, record);
    }

    pub fn has_channel(&self, peer: &R) -> bool {
        self.channels.contains_key(peer)
    }

    pub fn close_channel(&mut self, peer: &R) -> bool {
        self.channels.remove(peer).is_some()
    }

    pub fn close_all_channels(&mut self) -> usize {
        let count = self.channels.len();
        self.channels.clear();
        count
    }

    pub fn is_all_closed(&self) -> bool {
        self.channels.is_empty()
    }

    pub fn active_channel_count(&self) -> usize {
        self.channels.len()
    }

    pub fn local_role(&self) -> &R {
        &self.local_role
    }

    pub fn get_metadata(&self, peer: &R) -> Option<&SessionMetadata> {
        self.channels.get(peer).map(|record| &record.metadata)
    }

    pub fn all_metadata(&self) -> Vec<(R, &SessionMetadata)> {
        self.channels
            .iter()
            .map(|(peer, record)| (peer.clone(), &record.metadata))
            .collect()
    }
}

impl<R> Drop for TelltaleEndpoint<R>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    fn drop(&mut self) {
        let active = self.active_channel_count();
        if active > 0 {
            tracing::warn!(active, "Endpoint dropped with active channels; closing");
            self.close_all_channels();
        }
    }
}

/// Effect handler backed by Telltale sessions.
pub struct TelltaleHandler<R, M> {
    _phantom: PhantomData<(R, M)>,
}

impl<R, M> TelltaleHandler<R, M>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    async fn with_channel_operation<T, F, Fut>(
        ep: &mut TelltaleEndpoint<R>,
        peer: &R,
        default_description: &str,
        f: F,
    ) -> ChoreoResult<T>
    where
        F: FnOnce(ChannelState) -> Fut,
        Fut: std::future::Future<Output = ChoreoResult<(T, ChannelState, Option<String>, bool)>>,
    {
        let mut record = ep
            .take_record(peer)
            .ok_or_else(|| ChoreographyError::NoPeerChannel {
                peer: format!("{peer:?}"),
            })?;

        let (result, next_state, description, completed) = f(record.state).await?;
        record.state = next_state;
        record.metadata.operation_count += 1;
        record.metadata.state_description =
            description.unwrap_or_else(|| default_description.to_string());
        if completed {
            record.metadata.is_complete = true;
        }

        ep.put_record(peer.clone(), record);
        Ok(result)
    }
}

impl<R, M> Default for TelltaleHandler<R, M>
where
    R: Role + Eq + std::hash::Hash + Clone + Debug,
{
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl<R, M> ChoreoHandler for TelltaleHandler<R, M>
where
    R: Role<Message = M> + Send + Sync + RoleId + Eq + std::hash::Hash + Clone + Debug + 'static,
    M: Message<Box<dyn std::any::Any + Send>> + Send + Sync + 'static,
{
    type Role = R;
    type Endpoint = TelltaleEndpoint<R>;

    async fn send<Msg: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &Msg,
    ) -> ChoreoResult<()> {
        let serialized =
            bincode::serialize(msg).map_err(|e| ChoreographyError::MessageSerializationFailed {
                operation: "Serialization",
                type_name: std::any::type_name::<Msg>(),
                reason: e.to_string(),
            })?;

        Self::with_channel_operation(ep, &to, "Send", |state| async move {
            match state {
                ChannelState::Simple(mut channel) => {
                    channel.send(serialized).await.map_err(|e| {
                        ChoreographyError::ChannelSendFailed {
                            channel_type: "SimpleChannel",
                            reason: e,
                        }
                    })?;
                    Ok(((), ChannelState::Simple(channel), None, false))
                }
                ChannelState::Session(mut session) => {
                    let update = session.send(serialized).await?;
                    Ok((
                        (),
                        ChannelState::Session(session),
                        update.description,
                        update.is_complete,
                    ))
                }
            }
        })
        .await
    }

    async fn recv<Msg: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<Msg> {
        Self::with_channel_operation(ep, &from, "Recv", |state| async move {
            match state {
                ChannelState::Simple(mut channel) => {
                    let serialized =
                        channel
                            .recv()
                            .await
                            .map_err(|_| ChoreographyError::ChannelClosed {
                                channel_type: "SimpleChannel",
                                operation: "receive",
                            })?;
                    let msg = bincode::deserialize(&serialized).map_err(|e| {
                        ChoreographyError::MessageSerializationFailed {
                            operation: "Deserialization",
                            type_name: std::any::type_name::<Msg>(),
                            reason: e.to_string(),
                        }
                    })?;
                    Ok((msg, ChannelState::Simple(channel), None, false))
                }
                ChannelState::Session(mut session) => {
                    let update = session.recv().await?;
                    let msg = bincode::deserialize(&update.output).map_err(|e| {
                        ChoreographyError::MessageSerializationFailed {
                            operation: "Deserialization",
                            type_name: std::any::type_name::<Msg>(),
                            reason: e.to_string(),
                        }
                    })?;
                    Ok((
                        msg,
                        ChannelState::Session(session),
                        update.description,
                        update.is_complete,
                    ))
                }
            }
        })
        .await
    }

    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        who: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()> {
        let label_str = label.as_str().to_string();
        Self::with_channel_operation(ep, &who, "Choose", |state| async move {
            match state {
                ChannelState::Simple(mut channel) => {
                    let serialized = bincode::serialize(&label_str).map_err(|e| {
                        ChoreographyError::LabelSerializationFailed {
                            operation: "serialization",
                            reason: e.to_string(),
                        }
                    })?;
                    channel.send(serialized).await.map_err(|e| {
                        ChoreographyError::ChannelSendFailed {
                            channel_type: "SimpleChannel",
                            reason: e,
                        }
                    })?;
                    Ok(((), ChannelState::Simple(channel), None, false))
                }
                ChannelState::Session(mut session) => {
                    let update = session.choose(&label_str).await?;
                    Ok((
                        (),
                        ChannelState::Session(session),
                        update.description,
                        update.is_complete,
                    ))
                }
            }
        })
        .await
    }

    async fn offer(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
        Self::with_channel_operation(ep, &from, "Offer", |state| async move {
            match state {
                ChannelState::Simple(mut channel) => {
                    let serialized =
                        channel
                            .recv()
                            .await
                            .map_err(|_| ChoreographyError::ChannelClosed {
                                channel_type: "SimpleChannel",
                                operation: "offer",
                            })?;
                    let label_string: String = bincode::deserialize(&serialized).map_err(|e| {
                        ChoreographyError::LabelSerializationFailed {
                            operation: "deserialization",
                            reason: e.to_string(),
                        }
                    })?;
                    let label = <Self::Role as RoleId>::Label::from_str(&label_string).ok_or_else(
                        || {
                            ChoreographyError::ProtocolViolation(format!(
                                "Unknown label '{label_string}'"
                            ))
                        },
                    )?;
                    Ok((label, ChannelState::Simple(channel), None, false))
                }
                ChannelState::Session(mut session) => {
                    let update = session.offer().await?;
                    let label = <Self::Role as RoleId>::Label::from_str(&update.output)
                        .ok_or_else(|| {
                            ChoreographyError::ProtocolViolation(format!(
                                "Unknown label '{}'",
                                update.output
                            ))
                        })?;
                    Ok((
                        label,
                        ChannelState::Session(session),
                        update.description,
                        update.is_complete,
                    ))
                }
            }
        })
        .await
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        dur: Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send,
    {
        #[cfg(not(target_arch = "wasm32"))]
        {
            match tokio::time::timeout(dur, body).await {
                Ok(result) => result,
                Err(_) => Err(ChoreographyError::Timeout(dur)),
            }
        }

        #[cfg(target_arch = "wasm32")]
        {
            use futures::future::{select, Either};
            use futures::pin_mut;
            use wasm_timer::Delay;

            let timeout = Delay::new(dur);
            pin_mut!(body);
            pin_mut!(timeout);

            match select(body, timeout).await {
                Either::Left((result, _)) => result,
                Either::Right(_) => Err(ChoreographyError::Timeout(dur)),
            }
        }
    }
}
