impl ThreadedVM {
    /// Get the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        &self.trace
    }

    /// Get recorded effect-trace entries.
    #[must_use]
    pub fn effect_trace(&self) -> &[EffectTraceEntry] {
        &self.effect_trace
    }

    /// Deterministic communication replay-state root.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded VM lock is poisoned.
    ///
    #[must_use]
    pub fn communication_replay_root(&self) -> crate::verification::Hash {
        self.communication_consumption
            .lock()
            .expect("threaded VM lock poisoned")
            .root()
    }

    /// Receive-boundary replay-consumption artifacts.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded VM lock is poisoned.
    ///
    #[must_use]
    pub fn communication_consumption_artifacts(&self) -> Vec<CommunicationConsumptionArtifact> {
        self.communication_consumption_artifacts
            .lock()
            .expect("threaded VM lock poisoned")
            .clone()
    }

    /// Canonical replay/state fragment for deterministic diffing and snapshots.
    ///
    /// # Panics
    ///
    /// Panics if an internal threaded VM lock is poisoned.
    ///
    #[must_use]
    pub fn canonical_replay_fragment(&self) -> CanonicalReplayFragmentV1 {
        let communication_replay_root = self
            .communication_consumption
            .lock()
            .expect("threaded VM lock poisoned")
            .root();
        let communication_consumption_artifacts = self
            .communication_consumption_artifacts
            .lock()
            .expect("threaded VM lock poisoned")
            .clone();
        let corrupted_edges = self
            .corrupted_edges
            .iter()
            .map(|(edge, corruption)| (edge.clone(), *corruption))
            .collect();
        let timed_out_sites = self
            .timed_out_sites
            .iter()
            .map(|(site, until_tick)| (site.clone(), *until_tick))
            .collect();
        canonical_replay_fragment_v1(
            &self.trace,
            &self.effect_trace,
            self.crashed_sites.iter().cloned().collect(),
            self.partitioned_edges.iter().cloned().collect(),
            corrupted_edges,
            timed_out_sites,
            self.config.effect_determinism_tier,
            self.config.communication_replay_mode,
            Some(communication_replay_root),
            communication_consumption_artifacts,
        )
    }

    /// Get recorded output-condition verification checks.
    #[must_use]
    pub fn output_condition_checks(&self) -> &[OutputConditionCheck] {
        &self.output_condition_checks
    }

    /// Crashed sites currently active in topology state.
    #[must_use]
    pub fn crashed_sites(&self) -> &BTreeSet<String> {
        &self.crashed_sites
    }
}
