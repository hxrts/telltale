//! Transport trait and implementations for topology-aware communication.
//!
//! This module provides abstractions for different transport mechanisms:
//! - `InMemoryTransport`: In-process communication using channels
//! - `TcpTransport`: Network communication over TCP

use super::{
    validate_transport_contract_profile, DocumentedTransportContract, Location, Topology,
    TransportContractProfile, TransportContractTier, TransportOperationalContract,
    TransportSemanticContract, TransportStartupMode,
};
use crate::identifiers::RoleName;
use crate::mutex_lock;
#[cfg(not(target_arch = "wasm32"))]
use crate::runtime::spawn::spawn;
use crate::runtime::sync::{mpsc, Mutex};
use async_trait::async_trait;
use cfg_if::cfg_if;
#[cfg(target_arch = "wasm32")]
use futures::{SinkExt, StreamExt};
use std::collections::BTreeMap;
use std::sync::Arc;
#[cfg(not(target_arch = "wasm32"))]
use std::sync::{Mutex as StdMutex, OnceLock};
use thiserror::Error;

#[cfg(not(target_arch = "wasm32"))]
use tokio::io::{AsyncReadExt, AsyncWriteExt};
#[cfg(not(target_arch = "wasm32"))]
use tokio::net::{TcpListener, TcpStream};
#[cfg(not(target_arch = "wasm32"))]
use tokio::time::{sleep, Duration};

/// Errors that can occur during transport operations.
#[derive(Debug, Error)]
pub enum TransportError {
    #[error("connection failed: {0}")]
    ConnectionFailed(String),

    #[error("send failed: {0}")]
    SendFailed(String),

    #[error("receive failed: {0}")]
    ReceiveFailed(String),

    #[error("timeout")]
    Timeout,

    #[error("channel closed")]
    ChannelClosed,

    #[error("unknown role: {0}")]
    UnknownRole(RoleName),

    #[error("transport not ready")]
    NotReady,

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

/// Result type for transport operations.
pub type TransportResult<T> = Result<T, TransportError>;

/// A message that can be sent over a transport.
pub trait TransportMessage: Send + Sync + 'static {
    /// Serialize the message to bytes.
    fn to_bytes(&self) -> Vec<u8>;

    /// Deserialize from bytes.
    fn from_bytes(bytes: &[u8]) -> Result<Self, String>
    where
        Self: Sized;
}

/// Simple byte message for basic transport.
#[derive(Debug, Clone)]
pub struct ByteMessage(pub Vec<u8>);

impl TransportMessage for ByteMessage {
    fn to_bytes(&self) -> Vec<u8> {
        self.0.clone()
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        Ok(ByteMessage(bytes.to_vec()))
    }
}

/// Transport trait for sending and receiving messages between roles.
#[async_trait]
pub trait Transport: Send + Sync + 'static {
    /// Send a message to a specific role.
    async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()>;

    /// Receive a message from a specific role.
    async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>>;

    /// Check if the transport is connected to a role.
    fn is_connected(&self, role: &RoleName) -> bool;

    /// Close the transport connection.
    async fn close(&self) -> TransportResult<()>;
}

/// In-memory transport using channels.
///
/// This is the default transport for local testing where all roles
/// run in the same process.
pub struct InMemoryChannelTransport {
    /// Role this transport belongs to.
    role: RoleName,
    /// Sender channels to other roles (role -> sender).
    senders: Arc<Mutex<BTreeMap<RoleName, mpsc::Sender<Vec<u8>>>>>,
    /// Receiver channels from other roles (role -> receiver).
    receivers: Arc<Mutex<BTreeMap<RoleName, mpsc::Receiver<Vec<u8>>>>>,
}

impl InMemoryChannelTransport {
    /// Create a new in-memory transport for a role.
    pub fn new(role: RoleName) -> Self {
        Self {
            role,
            senders: Arc::new(Mutex::new(BTreeMap::new())),
            receivers: Arc::new(Mutex::new(BTreeMap::new())),
        }
    }

    /// Connect this transport to another role's transport.
    pub async fn connect(&self, other: &InMemoryChannelTransport) {
        let (tx1, rx1) = mpsc::channel(32);
        let (tx2, rx2) = mpsc::channel(32);

        // Self -> Other
        mutex_lock!(self.senders).insert(other.role.clone(), tx1);
        mutex_lock!(other.receivers).insert(self.role.clone(), rx1);

        // Other -> Self
        mutex_lock!(other.senders).insert(self.role.clone(), tx2);
        mutex_lock!(self.receivers).insert(other.role.clone(), rx2);
    }

    /// Get the role name.
    pub fn role(&self) -> &RoleName {
        &self.role
    }
}

impl DocumentedTransportContract for InMemoryChannelTransport {
    fn contract_profile() -> TransportContractProfile {
        TransportContractProfile {
            transport_name: "InMemoryChannelTransport",
            tier: TransportContractTier::FirstPartyRuntime,
            semantics: TransportSemanticContract {
                role_addressed_routing: true,
                per_peer_fifo_delivery: true,
                fail_closed_unknown_role: true,
                no_message_synthesis: true,
                explicit_readiness_errors: false,
                deterministic_for_regression: true,
            },
            operational: TransportOperationalContract {
                transport_type: TransportType::InMemory,
                startup_mode: TransportStartupMode::ReadyOnCreate,
                environment_resolved: false,
            },
            notes: vec![
                "In-process channel transport for first-party local execution.",
                "Deterministic enough for strict regression suites.",
            ],
        }
    }
}

#[async_trait]
impl Transport for InMemoryChannelTransport {
    async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()> {
        cfg_if! {
            if #[cfg(target_arch = "wasm32")] {
                // Clone the sender to release the lock before awaiting.
                let sender = {
                    let senders = mutex_lock!(self.senders);
                    senders
                        .get(to_role)
                        .cloned()
                        .ok_or_else(|| TransportError::UnknownRole(to_role.clone()))?
                };

                let mut sender = sender;
                sender
                    .send(message)
                    .await
                    .map_err(|_| TransportError::ChannelClosed)
            } else {
                let senders = mutex_lock!(self.senders);
                let sender = senders
                    .get(to_role)
                    .ok_or_else(|| TransportError::UnknownRole(to_role.clone()))?;

                sender
                    .send(message)
                    .await
                    .map_err(|_| TransportError::ChannelClosed)
            }
        }
    }

    async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>> {
        cfg_if! {
            if #[cfg(target_arch = "wasm32")] {
                // For WASM, take the receiver out so the lock is not held across `.await`.
                let mut receiver = {
                    let mut receivers = mutex_lock!(self.receivers);
                    receivers
                        .remove(from_role)
                        .ok_or_else(|| TransportError::UnknownRole(from_role.clone()))?
                };

                let result = receiver.next().await;

                {
                    let mut receivers = mutex_lock!(self.receivers);
                    receivers.insert(from_role.clone(), receiver);
                }

                result.ok_or(TransportError::ChannelClosed)
            } else {
                let mut receivers = mutex_lock!(self.receivers);
                let receiver = receivers
                    .get_mut(from_role)
                    .ok_or_else(|| TransportError::UnknownRole(from_role.clone()))?;
                receiver.recv().await.ok_or(TransportError::ChannelClosed)
            }
        }
    }

    fn is_connected(&self, _role: &RoleName) -> bool {
        // For in-memory, assume always connected after setup
        // In production, this should check if we have a sender for this role
        true
    }

    async fn close(&self) -> TransportResult<()> {
        mutex_lock!(self.senders).clear();
        mutex_lock!(self.receivers).clear();
        Ok(())
    }
}

#[cfg(not(target_arch = "wasm32"))]
enum TcpListenerState {
    NotStarted,
    Started,
    Failed(String),
}

#[cfg(not(target_arch = "wasm32"))]
struct TcpRoleState {
    role: RoleName,
    self_endpoint: Option<crate::identifiers::Endpoint>,
    inbound_senders: BTreeMap<RoleName, mpsc::Sender<Vec<u8>>>,
    inbound_receivers: Arc<Mutex<BTreeMap<RoleName, mpsc::Receiver<Vec<u8>>>>>,
    listener_state: Arc<Mutex<TcpListenerState>>,
}

#[cfg(not(target_arch = "wasm32"))]
impl TcpRoleState {
    fn new(
        role: RoleName,
        self_endpoint: Option<crate::identifiers::Endpoint>,
        peer_roles: impl IntoIterator<Item = RoleName>,
    ) -> Self {
        let mut inbound_senders = BTreeMap::new();
        let mut inbound_receivers = BTreeMap::new();
        for peer in peer_roles {
            let (tx, rx) = mpsc::channel(32);
            inbound_senders.insert(peer.clone(), tx);
            inbound_receivers.insert(peer, rx);
        }
        Self {
            role,
            self_endpoint,
            inbound_senders,
            inbound_receivers: Arc::new(Mutex::new(inbound_receivers)),
            listener_state: Arc::new(Mutex::new(TcpListenerState::NotStarted)),
        }
    }

    async fn ensure_started(self: &Arc<Self>) -> TransportResult<()> {
        let mut state = mutex_lock!(self.listener_state);
        match &*state {
            TcpListenerState::Started => return Ok(()),
            TcpListenerState::Failed(message) => {
                return Err(TransportError::ConnectionFailed(message.clone()));
            }
            TcpListenerState::NotStarted => {}
        }

        let Some(endpoint) = self.self_endpoint.clone() else {
            *state = TcpListenerState::Started;
            return Ok(());
        };

        let listener = TcpListener::bind(endpoint.as_str()).await.map_err(|err| {
            let message = format!(
                "failed to bind {} for role {}: {}",
                endpoint, self.role, err
            );
            *state = TcpListenerState::Failed(message.clone());
            TransportError::ConnectionFailed(message)
        })?;
        let role_state = Arc::clone(self);
        spawn(async move {
            role_state.accept_loop(listener).await;
        });
        *state = TcpListenerState::Started;
        Ok(())
    }

    async fn accept_loop(self: Arc<Self>, listener: TcpListener) {
        loop {
            let Ok((socket, _)) = listener.accept().await else {
                break;
            };
            let role_state = Arc::clone(&self);
            spawn(async move {
                let _ = role_state.handle_socket(socket).await;
            });
        }
    }

    async fn handle_socket(&self, mut socket: TcpStream) -> TransportResult<()> {
        let role_len = socket.read_u32().await? as usize;
        let mut role_buf = vec![0_u8; role_len];
        socket.read_exact(&mut role_buf).await?;
        let from_role = String::from_utf8(role_buf).map_err(|err| {
            TransportError::ReceiveFailed(format!("invalid sender header: {err}"))
        })?;
        let payload_len = socket.read_u32().await? as usize;
        let mut payload = vec![0_u8; payload_len];
        socket.read_exact(&mut payload).await?;
        let sender_role = RoleName::new(from_role.clone()).map_err(|err| {
            TransportError::ReceiveFailed(format!("invalid sender role `{from_role}`: {err}"))
        })?;
        let sender = self
            .inbound_senders
            .get(&sender_role)
            .cloned()
            .ok_or_else(|| {
                TransportError::ReceiveFailed(format!(
                    "sender role `{sender_role}` is not configured for {}",
                    self.role
                ))
            })?;
        sender
            .send(payload)
            .await
            .map_err(|_| TransportError::ChannelClosed)
    }

    async fn recv_from(&self, from_role: &RoleName) -> TransportResult<Vec<u8>> {
        let mut receivers = mutex_lock!(self.inbound_receivers);
        let receiver = receivers
            .get_mut(from_role)
            .ok_or_else(|| TransportError::UnknownRole(from_role.clone()))?;
        receiver.recv().await.ok_or(TransportError::ChannelClosed)
    }
}

#[cfg(not(target_arch = "wasm32"))]
type SharedTcpRegistry = BTreeMap<String, Arc<TcpRoleState>>;

#[cfg(not(target_arch = "wasm32"))]
fn shared_tcp_registry() -> &'static StdMutex<SharedTcpRegistry> {
    static REGISTRY: OnceLock<StdMutex<SharedTcpRegistry>> = OnceLock::new();
    REGISTRY.get_or_init(|| StdMutex::new(BTreeMap::new()))
}

#[cfg(not(target_arch = "wasm32"))]
fn tcp_role_registry_key(topology_signature: &str, role: &RoleName) -> String {
    format!("{topology_signature}|role:{role}")
}

#[cfg(not(target_arch = "wasm32"))]
fn shared_tcp_role_state(
    topology: &Topology,
    topology_signature: &str,
    role: &RoleName,
) -> TransportResult<Arc<TcpRoleState>> {
    let key = tcp_role_registry_key(topology_signature, role);
    let mut registry = shared_tcp_registry()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some(existing) = registry.get(&key) {
        return Ok(Arc::clone(existing));
    }

    let self_endpoint = match topology.get_location(role) {
        Ok(Location::Remote(endpoint)) => Some(endpoint),
        Ok(Location::Local | Location::Colocated(_)) => None,
        Err(_) => return Err(TransportError::UnknownRole(role.clone())),
    };
    let peer_roles = topology
        .locations
        .keys()
        .filter(|peer| *peer != role)
        .cloned();
    let state = Arc::new(TcpRoleState::new(role.clone(), self_endpoint, peer_roles));
    registry.insert(key, Arc::clone(&state));
    Ok(state)
}

#[cfg(not(target_arch = "wasm32"))]
async fn connect_with_retry(endpoint: &crate::identifiers::Endpoint) -> TransportResult<TcpStream> {
    let mut attempts = 0_u8;
    loop {
        match TcpStream::connect(endpoint.as_str()).await {
            Ok(stream) => return Ok(stream),
            Err(err) if attempts < 10 => {
                attempts = attempts.saturating_add(1);
                if err.kind() != std::io::ErrorKind::ConnectionRefused {
                    return Err(TransportError::ConnectionFailed(err.to_string()));
                }
                sleep(Duration::from_millis(10)).await;
            }
            Err(err) => return Err(TransportError::ConnectionFailed(err.to_string())),
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
struct TcpPeerTransport {
    state: Arc<TcpRoleState>,
    peer_role: RoleName,
    peer_endpoint: Option<crate::identifiers::Endpoint>,
}

#[cfg(not(target_arch = "wasm32"))]
impl DocumentedTransportContract for TcpPeerTransport {
    fn contract_profile() -> TransportContractProfile {
        TransportContractProfile {
            transport_name: "TcpPeerTransport",
            tier: TransportContractTier::FirstPartyRuntime,
            semantics: TransportSemanticContract {
                role_addressed_routing: true,
                per_peer_fifo_delivery: true,
                fail_closed_unknown_role: true,
                no_message_synthesis: true,
                explicit_readiness_errors: true,
                deterministic_for_regression: false,
            },
            operational: TransportOperationalContract {
                transport_type: TransportType::Tcp,
                startup_mode: TransportStartupMode::BackgroundWarmup,
                environment_resolved: false,
            },
            notes: vec![
                "Single-peer runtime TCP transport used for loopback remote topology execution.",
            ],
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
#[async_trait]
impl Transport for TcpPeerTransport {
    async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()> {
        if to_role != &self.peer_role {
            return Err(TransportError::UnknownRole(to_role.clone()));
        }
        let endpoint = self.peer_endpoint.clone().ok_or_else(|| {
            TransportError::ConnectionFailed(format!(
                "role {} has no remote endpoint configured for peer {}",
                self.state.role, self.peer_role
            ))
        })?;
        let mut stream = connect_with_retry(&endpoint).await?;
        let role_bytes = self.state.role.to_string().into_bytes();
        stream.write_u32(role_bytes.len() as u32).await?;
        stream.write_all(&role_bytes).await?;
        stream.write_u32(message.len() as u32).await?;
        stream.write_all(&message).await?;
        stream.shutdown().await?;
        Ok(())
    }

    async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>> {
        if from_role != &self.peer_role {
            return Err(TransportError::UnknownRole(from_role.clone()));
        }
        self.state.recv_from(from_role).await
    }

    fn is_connected(&self, role: &RoleName) -> bool {
        role == &self.peer_role
    }

    async fn close(&self) -> TransportResult<()> {
        Ok(())
    }
}

#[cfg(not(target_arch = "wasm32"))]
struct TcpRoleTransport {
    state: Arc<TcpRoleState>,
    peer_endpoints: BTreeMap<RoleName, Option<crate::identifiers::Endpoint>>,
}

#[cfg(not(target_arch = "wasm32"))]
impl DocumentedTransportContract for TcpRoleTransport {
    fn contract_profile() -> TransportContractProfile {
        TransportContractProfile {
            transport_name: "TcpRoleTransport",
            tier: TransportContractTier::FirstPartyRuntime,
            semantics: TransportSemanticContract {
                role_addressed_routing: true,
                per_peer_fifo_delivery: true,
                fail_closed_unknown_role: true,
                no_message_synthesis: true,
                explicit_readiness_errors: true,
                deterministic_for_regression: false,
            },
            operational: TransportOperationalContract {
                transport_type: TransportType::Tcp,
                startup_mode: TransportStartupMode::BackgroundWarmup,
                environment_resolved: false,
            },
            notes: vec![
                "Role-addressed runtime TCP transport used by the first-party topology helper.",
            ],
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
#[async_trait]
impl Transport for TcpRoleTransport {
    async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()> {
        self.state.ensure_started().await?;
        let endpoint = self
            .peer_endpoints
            .get(to_role)
            .cloned()
            .flatten()
            .ok_or_else(|| {
                TransportError::ConnectionFailed(format!(
                    "role {} has no remote endpoint configured for peer {}",
                    self.state.role, to_role
                ))
            })?;
        let mut stream = connect_with_retry(&endpoint).await?;
        let role_bytes = self.state.role.to_string().into_bytes();
        stream.write_u32(role_bytes.len() as u32).await?;
        stream.write_all(&role_bytes).await?;
        stream.write_u32(message.len() as u32).await?;
        stream.write_all(&message).await?;
        stream.shutdown().await?;
        Ok(())
    }

    async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>> {
        self.state.ensure_started().await?;
        self.state.recv_from(from_role).await
    }

    fn is_connected(&self, role: &RoleName) -> bool {
        self.peer_endpoints.contains_key(role)
    }

    async fn close(&self) -> TransportResult<()> {
        Ok(())
    }
}

#[cfg(not(target_arch = "wasm32"))]
pub(crate) async fn create_peer_transport(
    topology: &Topology,
    topology_signature: &str,
    role: &RoleName,
    peer: &RoleName,
) -> TransportResult<Box<dyn Transport>> {
    topology
        .region_for_role(role)
        .map_err(TransportError::ConnectionFailed)?;
    topology
        .region_for_role(peer)
        .map_err(TransportError::ConnectionFailed)?;
    let state = shared_tcp_role_state(topology, topology_signature, role)?;
    state.ensure_started().await?;
    let peer_endpoint = match topology.get_location(peer) {
        Ok(Location::Remote(endpoint)) => Some(endpoint),
        Ok(Location::Local | Location::Colocated(_)) => None,
        Err(_) => return Err(TransportError::UnknownRole(peer.clone())),
    };
    Ok(Box::new(TcpPeerTransport {
        state,
        peer_role: peer.clone(),
        peer_endpoint,
    }))
}

/// Factory for creating transports based on topology.
pub struct TransportFactory;

impl TransportFactory {
    fn validated_first_party_profile(
        profile: TransportContractProfile,
    ) -> TransportResult<TransportContractProfile> {
        validate_transport_contract_profile(&profile)
            .map_err(|err| TransportError::ConnectionFailed(err.to_string()))?;
        Ok(profile)
    }

    /// Return the documented first-party transport contract selected for a role/topology pair.
    pub fn contract_profile_for_topology(
        topology: &Topology,
        role: &RoleName,
    ) -> TransportResult<TransportContractProfile> {
        let has_remote_participants = topology
            .locations
            .values()
            .any(|location| matches!(location, Location::Remote(_)));
        if has_remote_participants {
            #[cfg(target_arch = "wasm32")]
            {
                let _ = (topology, role);
                Err(TransportError::NotReady)
            }
            #[cfg(not(target_arch = "wasm32"))]
            {
                topology
                    .region_for_role(role)
                    .map_err(TransportError::ConnectionFailed)?;
                Self::validated_first_party_profile(TcpRoleTransport::contract_profile())
            }
        } else {
            Self::validated_first_party_profile(InMemoryChannelTransport::contract_profile())
        }
    }

    /// Create a transport for a role based on the topology.
    pub fn create(topology: &Topology, role: &RoleName) -> TransportResult<Box<dyn Transport>> {
        let _profile = Self::contract_profile_for_topology(topology, role)?;
        let has_remote_participants = topology
            .locations
            .values()
            .any(|location| matches!(location, Location::Remote(_)));
        if has_remote_participants {
            #[cfg(target_arch = "wasm32")]
            {
                let _ = role;
                Err(TransportError::NotReady)
            }
            #[cfg(not(target_arch = "wasm32"))]
            {
                topology
                    .region_for_role(role)
                    .map_err(TransportError::ConnectionFailed)?;
                let state = shared_tcp_role_state(topology, "transport_factory", role)?;
                let warm_state = Arc::clone(&state);
                spawn(async move {
                    let _ = warm_state.ensure_started().await;
                });
                let peer_endpoints = topology
                    .locations
                    .iter()
                    .filter(|(peer, _)| *peer != role)
                    .map(|(peer, location)| {
                        let _ = topology
                            .region_for_role(peer)
                            .map_err(TransportError::ConnectionFailed)?;
                        let endpoint = match location {
                            Location::Remote(endpoint) => Some(endpoint.clone()),
                            Location::Local | Location::Colocated(_) => None,
                        };
                        Ok((peer.clone(), endpoint))
                    })
                    .collect::<TransportResult<BTreeMap<_, _>>>()?;
                Ok(Box::new(TcpRoleTransport {
                    state,
                    peer_endpoints,
                }))
            }
        } else {
            Ok(Box::new(InMemoryChannelTransport::new(role.clone())))
        }
    }

    /// Select transport type based on location.
    pub fn transport_for_location(
        _from_role: &RoleName,
        to_role: &RoleName,
        topology: &Topology,
    ) -> Result<TransportType, super::TopologyError> {
        match topology.get_location(to_role)? {
            Location::Local => Ok(TransportType::InMemory),
            Location::Colocated(_) => Ok(TransportType::SharedMemory),
            Location::Remote(_) => Ok(TransportType::Tcp),
        }
    }
}

/// Types of transport available.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransportType {
    /// In-process channels.
    InMemory,
    /// Shared memory (for colocated roles).
    SharedMemory,
    /// TCP network transport.
    Tcp,
    /// WebSocket transport.
    WebSocket,
}

impl TransportType {
    /// Check if this transport type is local (no network).
    pub fn is_local(&self) -> bool {
        matches!(self, TransportType::InMemory | TransportType::SharedMemory)
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_in_memory_transport() {
        let alice = InMemoryChannelTransport::new(RoleName::from_static("Alice"));
        let bob = InMemoryChannelTransport::new(RoleName::from_static("Bob"));

        alice.connect(&bob).await;

        // Alice sends to Bob
        alice
            .send(&RoleName::from_static("Bob"), b"Hello Bob".to_vec())
            .await
            .unwrap();

        // Bob receives from Alice
        let msg = bob.recv(&RoleName::from_static("Alice")).await.unwrap();
        assert_eq!(msg, b"Hello Bob".to_vec());

        // Bob sends to Alice
        bob.send(&RoleName::from_static("Alice"), b"Hello Alice".to_vec())
            .await
            .unwrap();

        // Alice receives from Bob
        let msg = alice.recv(&RoleName::from_static("Bob")).await.unwrap();
        assert_eq!(msg, b"Hello Alice".to_vec());
    }

    #[test]
    fn test_transport_type_for_location() {
        let topology = Topology::builder()
            .local_role(RoleName::from_static("Alice"))
            .remote_role(
                RoleName::from_static("Bob"),
                crate::identifiers::Endpoint::new("localhost:8080").unwrap(),
            )
            .colocated_role(
                RoleName::from_static("Carol"),
                RoleName::from_static("Alice"),
            )
            .build();

        assert_eq!(
            TransportFactory::transport_for_location(
                &RoleName::from_static("Alice"),
                &RoleName::from_static("Alice"),
                &topology
            )
            .unwrap(),
            TransportType::InMemory
        );
        assert_eq!(
            TransportFactory::transport_for_location(
                &RoleName::from_static("Alice"),
                &RoleName::from_static("Bob"),
                &topology
            )
            .unwrap(),
            TransportType::Tcp
        );
        assert_eq!(
            TransportFactory::transport_for_location(
                &RoleName::from_static("Alice"),
                &RoleName::from_static("Carol"),
                &topology
            )
            .unwrap(),
            TransportType::SharedMemory
        );
    }

    #[test]
    fn test_transport_type_is_local() {
        assert!(TransportType::InMemory.is_local());
        assert!(TransportType::SharedMemory.is_local());
        assert!(!TransportType::Tcp.is_local());
        assert!(!TransportType::WebSocket.is_local());
    }

    #[tokio::test]
    async fn test_transport_factory_create_supports_loopback_remote_topologies() {
        let local_topology = Topology::builder()
            .local_role(RoleName::from_static("Alice"))
            .local_role(RoleName::from_static("Bob"))
            .build();
        assert!(TransportFactory::create(&local_topology, &RoleName::from_static("Alice")).is_ok());

        let remote_topology = Topology::builder()
            .remote_role(
                RoleName::from_static("Alice"),
                crate::identifiers::Endpoint::new("127.0.0.1:19801").unwrap(),
            )
            .remote_role(
                RoleName::from_static("Bob"),
                crate::identifiers::Endpoint::new("127.0.0.1:19802").unwrap(),
            )
            .build();
        let alice = TransportFactory::create(&remote_topology, &RoleName::from_static("Alice"))
            .expect("remote transport for Alice");
        let bob = TransportFactory::create(&remote_topology, &RoleName::from_static("Bob"))
            .expect("remote transport for Bob");
        alice
            .send(&RoleName::from_static("Bob"), b"hello remote".to_vec())
            .await
            .expect("remote send");
        assert_eq!(
            bob.recv(&RoleName::from_static("Alice"))
                .await
                .expect("remote recv"),
            b"hello remote".to_vec()
        );
    }
}
