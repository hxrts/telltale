// Tests for session lifecycle, buffer operations, and auth trees.
    use serde_json::json;
    fn default_types() -> BTreeMap<String, LocalTypeR> {
        let mut m = BTreeMap::new();
        m.insert(
            "A".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Send {
                    partner: "B".into(),
                    branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                },
            ),
        );
        m.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Recv {
                    partner: "A".into(),
                    branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                },
            ),
        );
        m
    }

    fn single_send_recv_types() -> BTreeMap<String, LocalTypeR> {
        let mut types = BTreeMap::new();
        types.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
        );
        types.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End),
        );
        types
    }

    #[test]
    fn test_session_open_with_types() {
        let mut store = SessionStore::new();
        let types = default_types();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &types,
        );

        let ep_a = Endpoint {
            sid,
            role: "A".into(),
        };
        let ep_b = Endpoint {
            sid,
            role: "B".into(),
        };

        // Types should be unfolded (mu stripped).
        assert!(matches!(
            store.lookup_type(&ep_a),
            Some(LocalTypeR::Send { .. })
        ));
        assert!(matches!(
            store.lookup_type(&ep_b),
            Some(LocalTypeR::Recv { .. })
        ));
    }

    #[test]
    fn test_type_advance_and_unfold() {
        let mut store = SessionStore::new();
        let types = default_types();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &types,
        );

        let ep_a = Endpoint {
            sid,
            role: "A".into(),
        };

        // Get current type: Send { ... Var("step") }
        let lt = store
            .lookup_type(&ep_a)
            .expect("endpoint A should have an unfolded local type")
            .clone();
        let (_, _vt, continuation) = match &lt {
            LocalTypeR::Send { branches, .. } => branches
                .first()
                .expect("send branch list should contain the recursive continuation")
                .clone(),
            _ => panic!("expected Send"),
        };

        // Continuation is Var("step") — resolve it.
        let original = store
            .original_type(&ep_a)
            .expect("endpoint A should retain the original recursive local type");
        let resolved = unfold_if_var(&continuation, original);
        assert!(matches!(resolved, LocalTypeR::Send { .. }));

        // Advance type.
        store.update_type(&ep_a, resolved);
        assert!(matches!(
            store.lookup_type(&ep_a),
            Some(LocalTypeR::Send { .. })
        ));
    }

    #[test]
    fn test_branch_lookup_tracks_type_updates_and_removals() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let ep_a = Endpoint {
            sid,
            role: "A".into(),
        };

        let initial = store
            .get(sid)
            .expect("session exists")
            .lookup_branch_resolution(&ep_a, "msg")
            .expect("initial branch must be cached");
        assert_eq!(initial.direction, BranchDirection::Send);
        assert_eq!(initial.partner, "B");
        assert_eq!(initial.expected_type, None);

        store.update_type(
            &ep_a,
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("alt"), Some(ValType::Nat), LocalTypeR::End)],
            },
        );

        let updated_session = store.get(sid).expect("session exists after type update");
        assert!(updated_session
            .lookup_branch_resolution(&ep_a, "msg")
            .is_none());
        let updated = updated_session
            .lookup_branch_resolution(&ep_a, "alt")
            .expect("updated branch must be cached");
        assert_eq!(updated.direction, BranchDirection::Send);
        assert_eq!(updated.partner, "B");
        assert_eq!(updated.expected_type, Some(ValType::Nat));

        store.remove_type(&ep_a);
        assert!(store
            .get(sid)
            .expect("session exists after remove")
            .lookup_branch_resolution(&ep_a, "alt")
            .is_none());
    }

    #[test]
    fn test_session_send_recv() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
        );

        let session = store.get_mut(sid).expect("session should exist");
        session
            .send("A", "B", Value::Nat(42))
            .expect("single send/recv session should accept one enqueued value");
        assert!(session.has_message("A", "B"));
        assert!(!session.has_message("B", "A"));

        let val = session.recv("A", "B");
        assert_eq!(val, Some(Value::Nat(42)));
    }

    #[test]
    fn test_open_allocates_only_protocol_reachable_edges() {
        let mut types = BTreeMap::new();
        types.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
        );
        types.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End),
        );
        types.insert("C".to_string(), LocalTypeR::End);

        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into(), "C".into()],
            &BufferConfig::default(),
            &types,
        );

        let session = store.get_mut(sid).expect("session exists");
        assert_eq!(session.buffers.len(), 1);
        assert!(session.buffers.contains_key(&Edge::new(sid, "A", "B")));
        assert!(session.send("A", "B", Value::Nat(42)).is_ok());
        assert!(session.has_message("A", "B"));
        assert_eq!(session.recv("A", "B"), Some(Value::Nat(42)));
        assert_eq!(
            session.send("B", "A", Value::Nat(7)).unwrap_err(),
            "no buffer for edge B → A"
        );
        assert_eq!(
            session.send("A", "C", Value::Nat(9)).unwrap_err(),
            "no buffer for edge A → C"
        );
    }

    #[test]
    fn test_close_clears_buffers_and_traces_even_when_messages_pending() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
        );
        let edge = Edge::new(sid, "A", "B");
        store
            .get_mut(sid)
            .expect("session exists")
            .send("A", "B", Value::Nat(7))
            .expect("enqueue pending message");
        store.update_trace(&edge, vec![ValType::Nat]);

        store.close(sid).expect("close session");
        let session = store.get(sid).expect("session exists after close");
        assert_eq!(session.status, SessionStatus::Closed);
        assert!(session.buffers.is_empty());
        assert!(session.edge_traces.is_empty());
    }

    #[test]
    fn test_reap_closed_archives_and_removes_session() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );

        store.close(sid).expect("close session");
        let summaries = store.reap_closed();

        assert_eq!(summaries.len(), 1);
        assert_eq!(summaries[0].sid, sid);
        assert!(store.get(sid).is_none());
        assert_eq!(store.archived_closed().len(), 1);
    }

    #[test]
    fn test_memory_usage_tracks_live_and_archived_closed_sessions() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );

        let before_close = store.memory_usage();
        assert_eq!(before_close.live_sessions, 1);
        assert_eq!(before_close.live_closed_sessions, 0);
        assert!(before_close.retained_bytes.total > 0);
        assert!(before_close.retained_bytes.live_sessions > 0);
        assert!(before_close.retained_bytes.buffers > 0);

        store.close(sid).expect("close session");
        let after_close = store.memory_usage();
        assert_eq!(after_close.live_sessions, 1);
        assert_eq!(after_close.live_closed_sessions, 1);
        assert!(after_close.retained_bytes.total > 0);

        store.reap_closed();
        let after_reap = store.memory_usage();
        assert_eq!(after_reap.live_sessions, 0);
        assert_eq!(after_reap.live_closed_sessions, 0);
        assert_eq!(after_reap.archived_closed_sessions, 1);
        assert_eq!(after_reap.retained_bytes.live_sessions, 0);
        assert_eq!(after_reap.retained_bytes.local_types, 0);
        assert_eq!(after_reap.retained_bytes.buffers, 0);
        assert!(after_reap.retained_bytes.archived_closed > 0);
    }

    #[test]
    fn test_session_state_roundtrip_preserves_internal_role_edge_indexes() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into(), "C".into()],
            &BufferConfig::default(),
            &{
                let mut types = single_send_recv_types();
                types.insert("C".to_string(), LocalTypeR::End);
                types
            },
        );

        let session = store.get_mut(sid).expect("session exists");
        session.default_handler = "handler/default".to_string();
        session
            .edge_handlers
            .insert(Edge::new(sid, "A", "B"), "handler/ab".to_string());
        session.rebuild_derived_indexes();
        session
            .send("A", "B", Value::Nat(7))
            .expect("send should succeed");

        let encoded = bincode::serialize(session).expect("serialize session");
        let mut decoded: SessionState = bincode::deserialize(&encoded).expect("deserialize");

        assert_eq!(
            decoded.default_handler_binding().map(String::as_str),
            Some("handler/default")
        );
        assert_eq!(
            decoded
                .lookup_handler_for_roles("A", "B")
                .map(String::as_str),
            Some("handler/ab")
        );
        assert!(decoded.has_bound_handler());
        assert!(decoded
            .lookup_branch_resolution(
                &Endpoint {
                    sid,
                    role: "A".into()
                },
                "msg"
            )
            .is_some());
        assert!(decoded.has_message("A", "B"));
        assert_eq!(decoded.recv("A", "B"), Some(Value::Nat(7)));
        assert!(!decoded.has_message("A", "B"));
    }

    #[test]
    fn test_namespace_isolation() {
        let mut store = SessionStore::new();
        let sid1 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
        );
        let sid2 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
        );

        assert_ne!(sid1, sid2);

        store
            .get_mut(sid1)
            .expect("first session should exist")
            .send("A", "B", Value::Nat(1))
            .expect("send into first session should succeed");
        assert!(!store
            .get(sid2)
            .expect("second session should exist")
            .has_message("A", "B"));
    }

    #[test]
    fn test_remove_type() {
        let mut store = SessionStore::new();
        let types = default_types();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &types,
        );

        let ep_a = Endpoint {
            sid,
            role: "A".into(),
        };
        assert!(store.lookup_type(&ep_a).is_some());

        store.remove_type(&ep_a);
        assert!(store.lookup_type(&ep_a).is_none());
    }

    #[test]
    fn test_cross_session_role_name_edge_collision_regression() {
        let mut store = SessionStore::new();
        let sid1 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
        );
        let sid2 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
        );

        let e1 = Edge::new(sid1, "A", "B");
        let e2 = Edge::new(sid2, "A", "B");
        assert_ne!(e1, e2, "edges from distinct sessions must not collide");
        assert!(store
            .get(sid1)
            .expect("sid1 exists")
            .buffers
            .contains_key(&e1));
        assert!(store
            .get(sid2)
            .expect("sid2 exists")
            .buffers
            .contains_key(&e2));
    }

    #[test]
    fn test_edge_handler_and_trace_bindings() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );
        let edge = Edge::new(sid, "A", "B");
        let owner = store
            .claim_ownership(sid, "runtime/owner", OwnershipScope::Session)
            .expect("claim ownership");

        assert!(store.lookup_handler(&edge).is_none());
        assert_eq!(
            store.default_handler_for_session(sid).map(String::as_str),
            Some(DEFAULT_HANDLER_ID)
        );
        store
            .apply_owned_session_mutation(
                &owner,
                SessionHostMutation::UpdateEdgeHandler {
                    edge: edge.clone(),
                    handler: "handler/send".to_string(),
                },
            )
            .expect("owned edge handler update");
        assert_eq!(
            store.lookup_handler(&edge).map(String::as_str),
            Some("handler/send")
        );
        store
            .apply_owned_session_mutation(
                &owner,
                SessionHostMutation::SetDefaultHandler {
                    handler: "handler/default".to_string(),
                },
            )
            .expect("owned default handler update");
        assert_eq!(
            store.default_handler_for_session(sid).map(String::as_str),
            Some("handler/default")
        );
        assert!(
            store.get(sid).expect("session exists").has_bound_handler(),
            "internal handler ids must remain populated after updates"
        );

        assert!(store.lookup_trace(&edge).is_none());
        store
            .apply_owned_session_mutation(
                &owner,
                SessionHostMutation::UpdateTrace {
                    edge: edge.clone(),
                    trace: vec![ValType::Nat],
                },
            )
            .expect("owned trace update");
        assert_eq!(store.lookup_trace(&edge), Some([ValType::Nat].as_slice()));
    }

    #[test]
    fn test_claim_rejects_overlapping_owner() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );

        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("first claim should succeed");
        assert_eq!(owner.generation, 0);

        let err = store
            .claim_ownership(sid, "owner/b", OwnershipScope::Session)
            .expect_err("overlapping claim must fail");
        assert_eq!(
            err,
            OwnershipError::AlreadyClaimed {
                session_id: sid,
                current_owner_id: "owner/a".to_string(),
            }
        );
    }

    #[test]
    fn test_transfer_invalidates_prior_owner_handle() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let edge = Edge::new(sid, "A", "B");
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");
        let receipt = store
            .begin_ownership_transfer(&owner, "owner/b", OwnershipScope::Session)
            .expect("stage transfer");
        let new_owner = store
            .commit_ownership_transfer(&receipt)
            .expect("commit transfer");
        assert_eq!(new_owner.owner_id, "owner/b");
        assert_eq!(new_owner.generation, owner.generation + 1);

        let stale = store
            .apply_owned_session_mutation(
                &owner,
                SessionHostMutation::UpdateTrace {
                    edge: edge.clone(),
                    trace: vec![ValType::Nat],
                },
            )
            .expect_err("stale owner must fail");
        assert_eq!(
            stale,
            OwnershipError::StaleCapability {
                session_id: sid,
                owner_id: "owner/a".to_string(),
                expected_generation: 0,
                actual_generation: 1,
            }
        );

        store
            .apply_owned_session_mutation(
                &new_owner,
                SessionHostMutation::UpdateTrace {
                    edge,
                    trace: vec![ValType::Bool],
                },
            )
            .expect("new owner may mutate");
    }

    #[test]
    fn test_scope_attenuation_reuses_label_but_invalidates_generation() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let edge = Edge::new(sid, "A", "B");
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");

        let attenuated = store
            .attenuate_ownership_scope(
                &owner,
                OwnershipScope::Fragments(BTreeSet::from(["bundle/alpha".to_string()])),
            )
            .expect("attenuate scope");
        assert_eq!(attenuated.owner_id, owner.owner_id);
        assert_eq!(attenuated.generation, owner.generation + 1);

        let stale = store
            .apply_owned_session_mutation(
                &owner,
                SessionHostMutation::SetDefaultHandler {
                    handler: "handler/default".to_string(),
                },
            )
            .expect_err("old generation must be stale");
        assert_eq!(
            stale,
            OwnershipError::StaleCapability {
                session_id: sid,
                owner_id: "owner/a".to_string(),
                expected_generation: 0,
                actual_generation: 1,
            }
        );

        let scope_err = store
            .apply_owned_session_mutation(
                &attenuated,
                SessionHostMutation::UpdateTrace {
                    edge,
                    trace: vec![ValType::Nat],
                },
            )
            .expect_err("fragment scope must not mutate session-local host state");
        assert_eq!(
            scope_err,
            OwnershipError::ScopeViolation {
                session_id: sid,
                owner_id: "owner/a".to_string(),
                required: OwnershipScope::Session,
                actual: OwnershipScope::Fragments(BTreeSet::from([
                    "bundle/alpha".to_string()
                ])),
            }
        );
    }

    #[test]
    fn readiness_witness_is_generation_bound_and_single_use() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");
        let witness = store
            .issue_readiness_witness(&owner, "commit.ready")
            .expect("issue readiness witness");

        store
            .consume_readiness_witness(&owner, &witness)
            .expect("consume readiness witness");

        let reused = store
            .consume_readiness_witness(&owner, &witness)
            .expect_err("double use must fail");
        assert_eq!(
            reused,
            OwnershipError::WitnessConsumed {
                session_id: sid,
                witness_id: witness.witness_id,
            }
        );

        let audit = store.authority_audit_log(sid).expect("authority audit log");
        assert_eq!(audit.len(), 4);
        assert!(matches!(audit[0].artifact, AuthorityArtifact::OwnershipCapability(_)));
        assert_eq!(audit[0].event, AuthorityAuditEvent::Issued);
        assert!(matches!(audit[1].artifact, AuthorityArtifact::Readiness(_)));
        assert_eq!(audit[1].event, AuthorityAuditEvent::Issued);
        assert_eq!(audit[2].event, AuthorityAuditEvent::Consumed);
        assert_eq!(audit[3].event, AuthorityAuditEvent::Rejected);
    }

    #[test]
    fn readiness_witness_rejects_forged_and_stale_use() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");
        let witness = store
            .issue_readiness_witness(&owner, "commit.ready")
            .expect("issue readiness witness");

        let forged = ReadinessWitness {
            predicate_ref: "forged.ready".to_string(),
            ..witness.clone()
        };
        let forged_err = store
            .consume_readiness_witness(&owner, &forged)
            .expect_err("forged witness must fail");
        assert_eq!(
            forged_err,
            OwnershipError::InvalidWitness {
                session_id: sid,
                witness_id: witness.witness_id,
                reason: "witness payload mismatch".to_string(),
            }
        );

        let attenuated = store
            .attenuate_ownership_scope(
                &owner,
                OwnershipScope::Fragments(BTreeSet::from(["bundle/alpha".to_string()])),
            )
            .expect("attenuate scope");
        let stale_err = store
            .consume_readiness_witness(&attenuated, &witness)
            .expect_err("stale readiness witness must fail");
        assert_eq!(
            stale_err,
            OwnershipError::ScopeViolation {
                session_id: sid,
                owner_id: "owner/a".to_string(),
                required: OwnershipScope::Session,
                actual: OwnershipScope::Fragments(BTreeSet::from([
                    "bundle/alpha".to_string()
                ])),
            }
        );
    }

    #[test]
    fn test_transfer_rollback_is_claim_specific_and_preserves_current_owner() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let edge = Edge::new(sid, "A", "B");
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");
        let receipt = store
            .begin_ownership_transfer(
                &owner,
                "owner/b",
                OwnershipScope::Fragments(BTreeSet::from(["bundle/beta".to_string()])),
            )
            .expect("stage transfer");

        store
            .rollback_ownership_transfer(&receipt)
            .expect("rollback staged transfer");
        let session = store.get(sid).expect("session exists");
        assert!(session.ownership().pending_transfer.is_none());
        assert_eq!(
            session.ownership().current.as_ref(),
            Some(&owner),
            "rollback must preserve the preexisting current owner"
        );

        store
            .apply_owned_session_mutation(
                &owner,
                SessionHostMutation::UpdateTrace {
                    edge,
                    trace: vec![ValType::Nat],
                },
            )
            .expect("original owner must remain live after rollback");
    }

    #[test]
    fn ownership_release_rejects_pending_transfer_and_preserves_owner() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");
        let receipt = store
            .begin_ownership_transfer(&owner, "owner/b", OwnershipScope::Session)
            .expect("stage transfer");

        let err = store
            .release_ownership(&owner)
            .expect_err("release must fail while transfer is pending");
        assert_eq!(
            err,
            OwnershipError::TransferPending {
                session_id: sid,
                claim_id: receipt.claim_id,
            }
        );
        assert_eq!(
            store.current_ownership(sid),
            Some(&owner),
            "failed release must preserve the live owner capability"
        );
    }

    #[test]
    fn test_owner_death_faults_session_and_records_terminal_reason() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");

        let cancellation = store
            .mark_owner_died(sid, "owner/a")
            .expect("owner death should fault session");
        assert_eq!(cancellation.session_id, sid);
        assert_eq!(cancellation.owner_id, "owner/a");
        assert_eq!(
            cancellation.reason,
            OwnershipTerminalReason::OwnerDied {
                owner_id: "owner/a".to_string(),
            }
        );

        let session = store.get(sid).expect("session exists");
        assert_eq!(
            session.status,
            SessionStatus::Faulted {
                reason: "ownership owner `owner/a` died".to_string(),
            }
        );
        assert_eq!(
            session.ownership().terminal_reason,
            Some(OwnershipTerminalReason::OwnerDied {
                owner_id: "owner/a".to_string(),
            })
        );
    }

    #[test]
    fn test_abandoned_and_failed_transfer_are_terminal() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");
        let receipt = store
            .begin_ownership_transfer(&owner, "owner/b", OwnershipScope::Session)
            .expect("stage transfer");

        let cancelled_witness = store
            .cancel_abandoned_transfer(&receipt)
            .expect("abandoned transfer should cancel session");
        assert_eq!(cancelled_witness.session_id, sid);
        assert_eq!(cancelled_witness.owner_id, "owner/a");
        let cancelled = store.get(sid).expect("session exists");
        assert_eq!(cancelled.status, SessionStatus::Cancelled);
        assert_eq!(
            cancelled.ownership().terminal_reason,
            Some(OwnershipTerminalReason::TransferAbandoned {
                owner_id: "owner/a".to_string(),
                claim_id: receipt.claim_id,
            })
        );

        let sid2 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let owner2 = store
            .claim_ownership(sid2, "owner/c", OwnershipScope::Session)
            .expect("claim ownership");
        let receipt2 = store
            .begin_ownership_transfer(&owner2, "owner/d", OwnershipScope::Session)
            .expect("stage transfer");
        store
            .fault_failed_transfer_commit(&receipt2, "commit witness missing")
            .expect("failed transfer commit should fault session");
        let faulted = store.get(sid2).expect("session exists");
        assert_eq!(
            faulted.status,
            SessionStatus::Faulted {
                reason: "ownership transfer commit failed: commit witness missing".to_string(),
            }
        );
        assert_eq!(
            faulted.ownership().terminal_reason,
            Some(OwnershipTerminalReason::TransferCommitFailed {
                owner_id: "owner/c".to_string(),
                claim_id: receipt2.claim_id,
                reason: "commit witness missing".to_string(),
            })
        );
    }

    #[test]
    fn stale_and_forged_transfer_receipts_fail_closed_and_audit_rejection() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");
        let receipt = store
            .begin_ownership_transfer(&owner, "owner/b", OwnershipScope::Session)
            .expect("stage transfer");

        let _committed = store
            .commit_ownership_transfer(&receipt)
            .expect("commit transfer");

        let reused = store
            .commit_ownership_transfer(&receipt)
            .expect_err("reused receipt must fail closed");
        assert!(matches!(
            reused,
            OwnershipError::TransferNotPending { session_id } if session_id == sid
        ));

        let live_owner = store
            .current_ownership(sid)
            .expect("current owner after committed transfer")
            .clone();
        let staged = store
            .begin_ownership_transfer(&live_owner, "owner/c", OwnershipScope::Session)
            .expect("stage second transfer");
        let forged = OwnershipReceipt {
            claim_id: staged.claim_id.saturating_add(99),
            ..staged.clone()
        };
        let mismatch = store
            .rollback_ownership_transfer(&forged)
            .expect_err("forged receipt must fail closed");
        assert!(matches!(
            mismatch,
            OwnershipError::ReceiptMismatch {
                session_id,
                claim_id,
                ..
            } if session_id == sid && claim_id == forged.claim_id
        ));

        let audit = store.authority_audit_log(sid).expect("authority audit log");
        let rejected_receipts: Vec<_> = audit
            .iter()
            .filter_map(|record| match (&record.artifact, record.event) {
                (AuthorityArtifact::OwnershipReceipt(audit_receipt), AuthorityAuditEvent::Rejected) => {
                    Some(audit_receipt.claim_id)
                }
                _ => None,
            })
            .collect();
        assert!(
            rejected_receipts.contains(&receipt.claim_id),
            "reused receipt should emit a rejected audit record"
        );
        assert!(
            rejected_receipts.contains(&forged.claim_id),
            "forged receipt should emit a rejected audit record"
        );
    }

    #[test]
    fn ownership_terminal_session_rejects_reclaim_and_mutation() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let edge = Edge::new(sid, "A", "B");
        let owner = store
            .claim_ownership(sid, "owner/a", OwnershipScope::Session)
            .expect("claim ownership");
        let receipt = store
            .begin_ownership_transfer(&owner, "owner/b", OwnershipScope::Session)
            .expect("stage transfer");

        store
            .cancel_abandoned_transfer(&receipt)
            .expect("abandoned transfer should terminate session");

        let reclaim = store
            .claim_ownership(sid, "owner/c", OwnershipScope::Session)
            .expect_err("terminal session must reject reclaim");
        assert_eq!(
            reclaim,
            OwnershipError::Terminal {
                session_id: sid,
                reason: OwnershipTerminalReason::TransferAbandoned {
                    owner_id: "owner/a".to_string(),
                    claim_id: receipt.claim_id,
                },
            }
        );

        let mutate = store
            .apply_owned_session_mutation(
                &owner,
                SessionHostMutation::UpdateTrace {
                    edge,
                    trace: vec![ValType::Nat],
                },
            )
            .expect_err("terminal session must reject stale host mutation");
        assert_eq!(
            mutate,
            OwnershipError::Terminal {
                session_id: sid,
                reason: OwnershipTerminalReason::TransferAbandoned {
                    owner_id: "owner/a".to_string(),
                    claim_id: receipt.claim_id,
                },
            }
        );
    }

    #[test]
    fn test_decode_edge_json_requires_sid_sender_receiver() {
        let sid_qualified = json!({
            "sid": 7,
            "sender": "A",
            "receiver": "B"
        });
        let e = decode_edge_json(&sid_qualified, None).expect("decode sid-qualified edge");
        assert_eq!(e, Edge::new(7, "A", "B"));

        let no_sid = json!({
            "sender": "A",
            "receiver": "B"
        });
        let e2 = decode_edge_json(&no_sid, Some(11)).expect("decode edge with sid hint");
        assert_eq!(e2, Edge::new(11, "A", "B"));

    }
