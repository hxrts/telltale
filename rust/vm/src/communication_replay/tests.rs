#[cfg(test)]
mod tests {
    use super::*;

    fn sample_identity(sequence_no: u64) -> CommunicationIdentity {
        let edge = Edge::new(7, "A", "B");
        CommunicationIdentity::from_payload(
            &edge,
            CommunicationStepKind::Receive,
            "msg",
            &Value::Nat(3),
            sequence_no,
        )
    }

    #[test]
    fn off_mode_accepts_duplicate_identities() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Off);
        let identity = sample_identity(0);
        assert!(model.consume_receive(&identity).is_ok());
        assert!(model.consume_receive(&identity).is_ok());
    }

    #[test]
    fn sequence_mode_accepts_in_order_messages() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Sequence);
        assert!(model.consume_receive(&sample_identity(0)).is_ok());
        assert!(model.consume_receive(&sample_identity(1)).is_ok());
    }

    #[test]
    fn sequence_mode_rejects_out_of_order_messages() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Sequence);
        let first = sample_identity(0);
        let second = sample_identity(2);
        assert!(model.consume_receive(&first).is_ok());
        let err = model
            .consume_receive(&second)
            .expect_err("out-of-order sequence should fail");
        assert_eq!(err.tag(), COMM_REPLAY_SEQUENCE_MISMATCH_TAG);
    }

    #[test]
    fn nullifier_mode_rejects_duplicate_identities() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Nullifier);
        let identity = sample_identity(5);
        assert!(model.consume_receive(&identity).is_ok());
        let err = model
            .consume_receive(&identity)
            .expect_err("duplicate identity should fail");
        assert_eq!(err.tag(), COMM_REPLAY_DUPLICATE_TAG);
    }

    #[test]
    fn canonical_receive_label_uses_typed_context_when_available() {
        let label = canonical_receive_label_context("msg", Some(&ValType::Nat));
        assert_eq!(label, "recv:Nat");
    }

    #[test]
    fn canonical_receive_label_falls_back_to_runtime_label_when_untyped() {
        let label = canonical_receive_label_context("msg", None);
        assert_eq!(label, "msg");
    }

    #[test]
    fn identity_seed_matches_direct_identity_construction() {
        let edge = Edge::new(7, "A", "B");
        let seed = CommunicationIdentitySeed::new(&edge, CommunicationStepKind::Receive, "msg");
        let payload = Value::Prod(Box::new(Value::Nat(3)), Box::new(Value::Bool(true)));
        assert_eq!(
            seed.build(&payload, 5),
            CommunicationIdentity::from_payload(
                &edge,
                CommunicationStepKind::Receive,
                "msg",
                &payload,
                5,
            )
        );
    }

    #[test]
    fn cached_replay_root_matches_state_root_after_updates() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Sequence);
        let edge = Edge::new(7, "A", "B");
        assert_eq!(model.root(), model.state().root());

        let _sequence = model.allocate_send_sequence(&edge);
        assert_eq!(model.root(), model.state().root());

        assert!(model.consume_receive(&sample_identity(0)).is_ok());
        assert_eq!(model.root(), model.state().root());

        model.set_mode(CommunicationReplayMode::Nullifier);
        assert!(model.consume_receive(&sample_identity(9)).is_ok());
        assert_eq!(model.root(), model.state().root());

        model.prune_session(7);
        assert_eq!(model.root(), model.state().root());
    }

    #[test]
    fn cached_replay_root_survives_roundtrip() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Nullifier);
        let edge = Edge::new(7, "A", "B");
        let _sequence = model.allocate_send_sequence(&edge);
        assert!(model.consume_receive(&sample_identity(5)).is_ok());

        let encoded = bincode::serialize(&model).expect("serialize replay consumption");
        let decoded: DefaultCommunicationConsumption =
            bincode::deserialize(&encoded).expect("deserialize replay consumption");

        assert_eq!(decoded.root(), decoded.state().root());
        assert_eq!(decoded, model);
    }
}
