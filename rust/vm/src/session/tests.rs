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
        let lt = store.lookup_type(&ep_a).unwrap().clone();
        let (_, _vt, continuation) = match &lt {
            LocalTypeR::Send { branches, .. } => branches.first().unwrap().clone(),
            _ => panic!("expected Send"),
        };

        // Continuation is Var("step") — resolve it.
        let original = store.original_type(&ep_a).unwrap();
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

        let session = store.get_mut(sid).unwrap();
        session.send("A", "B", Value::Nat(42)).unwrap();
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
            .unwrap()
            .send("A", "B", Value::Nat(1))
            .unwrap();
        assert!(!store.get(sid2).unwrap().has_message("A", "B"));
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

        assert!(store.lookup_handler(&edge).is_none());
        assert_eq!(
            store.default_handler_for_session(sid).map(String::as_str),
            Some(DEFAULT_HANDLER_ID)
        );
        store.update_handler(&edge, "handler/send".to_string());
        assert_eq!(
            store.lookup_handler(&edge).map(String::as_str),
            Some("handler/send")
        );
        store.set_default_handler_for_session(sid, "handler/default".to_string());
        assert_eq!(
            store.default_handler_for_session(sid).map(String::as_str),
            Some("handler/default")
        );
        assert!(
            store.get(sid).expect("session exists").has_bound_handler(),
            "internal handler ids must remain populated after updates"
        );

        assert!(store.lookup_trace(&edge).is_none());
        store.update_trace(&edge, vec![ValType::Nat]);
        assert_eq!(store.lookup_trace(&edge), Some([ValType::Nat].as_slice()));
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

        let legacy = json!({
            "from": "A",
            "to": "B",
            "sid": 11
        });
        let err = decode_edge_json(&legacy, None).expect_err("legacy edge shape must be rejected");
        assert!(err.contains("invalid edge json"), "unexpected error: {err}");
    }
