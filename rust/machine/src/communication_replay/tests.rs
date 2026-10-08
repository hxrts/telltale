// Tests for communication replay modes and nullifier enforcement.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::verification::{DefaultVerificationModel, VerificationModel};

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

    fn test_crypto_hash(tag: HashTag, bytes: &[u8]) -> Hash {
        // Deterministic stand-in for an embedder-supplied hash, distinct from the default.
        let mut out = [0_u8; 32];
        let mut state: u64 = 0xcbf2_9ce4_8422_2325 ^ u64::from(tag.domain_byte());
        for (index, byte) in bytes.iter().enumerate() {
            state ^= u64::from(*byte);
            state = state.wrapping_mul(0x0000_0100_0000_01b3);
            out[index % 32] ^= state.to_le_bytes()[index % 8];
        }
        for slot in &mut out {
            state = state.rotate_left(7).wrapping_add(1);
            *slot ^= state.to_le_bytes()[0];
        }
        Hash(out)
    }

    const TEST_MODEL: HashModel = HashModel::new("test.crypto.v1", test_crypto_hash);

    #[test]
    fn custom_hash_model_differs_from_default_and_is_deterministic() {
        let bytes = b"telltale";
        let custom = TEST_MODEL.hash(HashTag::Nullifier, bytes);
        assert_eq!(custom, TEST_MODEL.hash(HashTag::Nullifier, bytes));
        assert_ne!(custom, HashModel::DEFAULT.hash(HashTag::Nullifier, bytes));
        assert_ne!(custom, TEST_MODEL.hash(HashTag::Value, bytes));
        assert_eq!(
            HashModel::DEFAULT.hash(HashTag::Nullifier, bytes),
            DefaultVerificationModel::hash(HashTag::Nullifier, bytes)
        );
        assert_eq!(
            HashModel::from_verification_model::<DefaultVerificationModel>("alias"),
            HashModel::new("alias", test_crypto_hash),
            "models compare by identifier"
        );
    }

    #[test]
    fn custom_hash_model_changes_nullifiers_and_roots_deterministically() {
        let identity = sample_identity(5);
        let mut default = DefaultCommunicationConsumption::new(CommunicationReplayMode::Nullifier);
        let mut custom = DefaultCommunicationConsumption::with_models(
            CommunicationReplayMode::Nullifier,
            CommunicationNullifierIdentity::SequenceBound,
            TEST_MODEL,
        );
        let mut custom_again = custom.clone();
        let default_nullifier = default
            .consume_receive(&identity)
            .expect("default consume")
            .consumed_nullifier;
        let custom_result = custom.consume_receive(&identity).expect("custom consume");
        let custom_again_result = custom_again
            .consume_receive(&identity)
            .expect("custom consume");
        assert_ne!(custom_result.consumed_nullifier, default_nullifier);
        assert_eq!(custom_result, custom_again_result);
        assert_ne!(custom.root(), default.root());
        assert_eq!(custom.root(), custom.state().root_with(TEST_MODEL));
    }

    #[test]
    fn default_identity_nullifier_is_unchanged() {
        let identity = sample_identity(5);
        let expected = Nullifier(DefaultVerificationModel::hash(
            HashTag::Nullifier,
            &replay_binary_encode(&identity),
        ));
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Nullifier);
        assert_eq!(
            model.nullifier_identity(),
            CommunicationNullifierIdentity::SequenceBound
        );
        assert!(model.hash_model().is_default());
        let consumed = model
            .consume_receive(&identity)
            .expect("consume")
            .consumed_nullifier;
        assert_eq!(consumed, Some(expected));
        // Sequence-bound identity accepts identical content with a new sequence.
        assert!(model.consume_receive(&sample_identity(6)).is_ok());
    }

    #[test]
    fn content_only_identity_ignores_sequence_and_rejects_resend() {
        for hash_model in [HashModel::DEFAULT, TEST_MODEL] {
            let content = CommunicationNullifierIdentity::ContentOnly;
            assert_eq!(
                content.nullifier(&sample_identity(5), hash_model),
                content.nullifier(&sample_identity(99), hash_model)
            );
            assert_ne!(
                content.nullifier(&sample_identity(5), hash_model),
                CommunicationNullifierIdentity::SequenceBound
                    .nullifier(&sample_identity(5), hash_model)
            );
            let mut model = DefaultCommunicationConsumption::with_models(
                CommunicationReplayMode::Nullifier,
                content,
                hash_model,
            );
            let first = model
                .consume_receive(&sample_identity(5))
                .expect("first receive")
                .consumed_nullifier
                .expect("nullifier consumed");
            let err = model
                .consume_receive(&sample_identity(6))
                .expect_err("resend with fresh sequence must be rejected");
            assert_eq!(
                err,
                CommunicationReplayError::DuplicateIdentity { nullifier: first }
            );
            let other_payload = CommunicationIdentity::from_payload(
                &Edge::new(7, "A", "B"),
                CommunicationStepKind::Receive,
                "msg",
                &Value::Nat(4),
                7,
            );
            assert!(model.consume_receive(&other_payload).is_ok());
        }
    }

    #[test]
    fn prune_session_retains_consumed_nullifiers() {
        let mut model = DefaultCommunicationConsumption::with_models(
            CommunicationReplayMode::Nullifier,
            CommunicationNullifierIdentity::ContentOnly,
            TEST_MODEL,
        );
        assert!(model.consume_receive(&sample_identity(0)).is_ok());
        model.prune_session(7);
        assert_eq!(
            model
                .consume_receive(&sample_identity(1))
                .expect_err("pruned session must not re-admit identity")
                .tag(),
            COMM_REPLAY_DUPLICATE_TAG
        );
    }

    #[test]
    fn content_only_identity_roundtrips_and_custom_model_fails_closed() {
        let model = DefaultCommunicationConsumption::with_models(
            CommunicationReplayMode::Nullifier,
            CommunicationNullifierIdentity::ContentOnly,
            HashModel::DEFAULT,
        );
        let decoded: DefaultCommunicationConsumption =
            bincode::deserialize(&bincode::serialize(&model).expect("serialize"))
                .expect("deserialize");
        assert_eq!(decoded, model);

        let custom = DefaultCommunicationConsumption::with_models(
            CommunicationReplayMode::Nullifier,
            CommunicationNullifierIdentity::ContentOnly,
            TEST_MODEL,
        );
        let encoded = serde_json::to_string(&custom).expect("serialize");
        assert!(serde_json::from_str::<DefaultCommunicationConsumption>(&encoded).is_err());
    }
}
