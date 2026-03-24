/// Replay-consumption error.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CommunicationReplayError {
    /// Received sequence number does not match expected edge position.
    SequenceMismatch {
        /// Expected sequence number.
        expected: u64,
        /// Received sequence number.
        actual: u64,
    },
    /// Identity nullifier was already consumed.
    DuplicateIdentity {
        /// Duplicate nullifier.
        nullifier: Nullifier,
    },
}

impl CommunicationReplayError {
    /// Stable deterministic error tag.
    #[must_use]
    pub fn tag(&self) -> &'static str {
        match self {
            Self::SequenceMismatch { .. } => COMM_REPLAY_SEQUENCE_MISMATCH_TAG,
            Self::DuplicateIdentity { .. } => COMM_REPLAY_DUPLICATE_TAG,
        }
    }
}

/// Replay-consumption check result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommunicationConsumeResult {
    /// Mode used for the check.
    pub mode: CommunicationReplayMode,
    /// Replay-state root before check.
    pub pre_root: Hash,
    /// Replay-state root after check.
    pub post_root: Hash,
    /// Consumed nullifier when mode is `Nullifier`.
    pub consumed_nullifier: Option<Nullifier>,
}

/// Proof-friendly replay-consumption artifact recorded at receive boundaries.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommunicationConsumptionArtifact {
    /// Scheduler tick at consumption time.
    pub tick: u64,
    /// Canonical identity consumed at receive.
    pub identity: CommunicationIdentity,
    /// Active replay mode.
    pub mode: CommunicationReplayMode,
    /// Replay-state root before receive consumption.
    pub pre_root: Hash,
    /// Replay-state root after receive consumption.
    pub post_root: Hash,
}

/// Replay-consumption interface for send/receive boundaries.
pub trait CommunicationConsumption {
    /// Active replay mode.
    fn mode(&self) -> CommunicationReplayMode;
    /// Set active replay mode.
    fn set_mode(&mut self, mode: CommunicationReplayMode);
    /// Read replay-consumption state.
    fn state(&self) -> &CommunicationReplayState;
    /// Read the deterministic replay-state root.
    fn root(&self) -> Hash;
    /// Allocate next outbound sequence number for an edge.
    fn allocate_send_sequence(&mut self, edge: &Edge) -> u64;
    /// Consume a receive identity according to the selected mode.
    ///
    /// # Errors
    ///
    /// Returns [`CommunicationReplayError`] when the active mode rejects the
    /// receive identity (for example, sequence mismatch or duplicate identity).
    fn consume_receive(
        &mut self,
        identity: &CommunicationIdentity,
    ) -> Result<CommunicationConsumeResult, CommunicationReplayError>;
    /// Drop replay-tracker state for a closed session.
    fn prune_session(&mut self, sid: SessionId);
}

/// Default replay-consumption implementation used by the VM.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DefaultCommunicationConsumption {
    /// Configured mode.
    #[serde(default)]
    pub mode: CommunicationReplayMode,
    /// Deterministic replay state.
    #[serde(default)]
    pub state: CommunicationReplayState,
    /// Incrementally maintained replay root cache.
    #[serde(skip)]
    root_cache: ReplayRootCache,
}

impl DefaultCommunicationConsumption {
    /// Create a replay-consumption model in `mode`.
    #[must_use]
    pub fn new(mode: CommunicationReplayMode) -> Self {
        let mut model = Self {
            mode,
            state: CommunicationReplayState::default(),
            root_cache: ReplayRootCache::default(),
        };
        model.rebuild_root_cache();
        model
    }

    /// Deterministic replay root using the cached incremental path.
    #[must_use]
    pub fn root(&self) -> Hash {
        self.root_cache.root()
    }

    fn rebuild_root_cache(&mut self) {
        self.root_cache = ReplayRootCache::from_state(&self.state);
    }
}

fn identity_nullifier(identity: &CommunicationIdentity) -> Nullifier {
    let bytes = replay_binary_encode(identity);
    Nullifier(DefaultVerificationModel::hash(HashTag::Nullifier, &bytes))
}

#[derive(Debug, Deserialize)]
struct DefaultCommunicationConsumptionSerde {
    #[serde(default)]
    mode: CommunicationReplayMode,
    #[serde(default)]
    state: CommunicationReplayState,
}

impl<'de> Deserialize<'de> for DefaultCommunicationConsumption {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let raw = DefaultCommunicationConsumptionSerde::deserialize(deserializer)?;
        let mut model = Self {
            mode: raw.mode,
            state: raw.state,
            root_cache: ReplayRootCache::default(),
        };
        model.rebuild_root_cache();
        Ok(model)
    }
}

impl CommunicationConsumption for DefaultCommunicationConsumption {
    fn mode(&self) -> CommunicationReplayMode {
        self.mode
    }

    fn set_mode(&mut self, mode: CommunicationReplayMode) {
        self.mode = mode;
    }

    fn state(&self) -> &CommunicationReplayState {
        &self.state
    }

    fn root(&self) -> Hash {
        DefaultCommunicationConsumption::root(self)
    }

    fn allocate_send_sequence(&mut self, edge: &Edge) -> u64 {
        let previous = self.state.next_send_sequence.get(edge).copied();
        let entry = self
            .state
            .next_send_sequence
            .entry(edge.clone())
            .or_insert(0);
        let sequence_no = *entry;
        *entry = entry.saturating_add(1);
        self.root_cache.update_send_sequence(edge, previous, *entry);
        sequence_no
    }

    fn consume_receive(
        &mut self,
        identity: &CommunicationIdentity,
    ) -> Result<CommunicationConsumeResult, CommunicationReplayError> {
        let pre_root = self.root();
        let consumed_nullifier = match self.mode {
            CommunicationReplayMode::Off => None,
            CommunicationReplayMode::Sequence => {
                let edge = identity.edge();
                let expected = self
                    .state
                    .next_recv_sequence
                    .get(&edge)
                    .copied()
                    .unwrap_or(0);
                if identity.sequence_no != expected {
                    return Err(CommunicationReplayError::SequenceMismatch {
                        expected,
                        actual: identity.sequence_no,
                    });
                }
                let previous = self.state.next_recv_sequence.get(&edge).copied();
                self.state
                    .next_recv_sequence
                    .insert(edge, expected.saturating_add(1));
                self.root_cache.update_recv_sequence(
                    &identity.edge(),
                    previous,
                    expected.saturating_add(1),
                );
                None
            }
            CommunicationReplayMode::Nullifier => {
                let nullifier = identity_nullifier(identity);
                if self.state.consumed_nullifiers.contains(&nullifier) {
                    return Err(CommunicationReplayError::DuplicateIdentity { nullifier });
                }
                self.state.consumed_nullifiers.insert(nullifier);
                self.root_cache.insert_nullifier(nullifier);
                Some(nullifier)
            }
        };
        let post_root = self.root();
        Ok(CommunicationConsumeResult {
            mode: self.mode,
            pre_root,
            post_root,
            consumed_nullifier,
        })
    }

    fn prune_session(&mut self, sid: SessionId) {
        let send_pruned: Vec<_> = self
            .state
            .next_send_sequence
            .iter()
            .filter_map(|(edge, sequence_no)| {
                (edge.sid == sid).then_some((edge.clone(), *sequence_no))
            })
            .collect();
        let recv_pruned: Vec<_> = self
            .state
            .next_recv_sequence
            .iter()
            .filter_map(|(edge, sequence_no)| {
                (edge.sid == sid).then_some((edge.clone(), *sequence_no))
            })
            .collect();
        self.state
            .next_send_sequence
            .retain(|edge, _| edge.sid != sid);
        self.state
            .next_recv_sequence
            .retain(|edge, _| edge.sid != sid);
        for (edge, sequence_no) in send_pruned {
            self.root_cache.remove_send_sequence(&edge, sequence_no);
        }
        for (edge, sequence_no) in recv_pruned {
            self.root_cache.remove_recv_sequence(&edge, sequence_no);
        }
    }
}
