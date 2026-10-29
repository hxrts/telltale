fn allocation_image() -> CodeImage {
    CodeImage {
        programs: BTreeMap::from([("A".into(), vec![Instr::Halt])]),
        global_type: telltale_types::GlobalType::End,
        local_types: BTreeMap::from([("A".into(), LocalTypeR::End)]),
    }
}

#[test]
fn owned_loader_exhaustion_preserves_original_session_owner_and_clock() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let image = allocation_image();
    let owner = machine
        .load_choreography_owned(&image, "original")
        .expect("actual preferred owner");
    machine
        .sessions
        .open_with_sid(
            usize::MAX - 1,
            vec!["A".into()],
            &BufferConfig::default(),
            &image.local_types,
        )
        .expect("last explicit fresh allocation");
    machine.next_session_id = machine.sessions.next_session_id();
    let before = crate::serialization::binary_encode(&machine).expect("actual complete machine");
    let failure = machine.load_choreography_owned(&image, "original");
    let source_is_exhausted = failure
        .as_ref()
        .err()
        .and_then(|error| std::error::Error::source(error))
        .and_then(|source| source.downcast_ref::<crate::session::SessionAllocationError>())
        == Some(&crate::session::SessionAllocationError::Exhausted);
    assert!(
        source_is_exhausted,
        "missing original allocation source: {failure:?}"
    );
    assert!(matches!(
        failure,
        Err(ProtocolMachineError::SessionAllocation(
            crate::session::SessionAllocationError::Exhausted
        ))
    ));
    assert_eq!(
        crate::serialization::binary_encode(&machine).unwrap(),
        before
    );
    assert!(
        crate::owned::OwnedSessionMachine::validate_owned_operation(&mut machine, &owner).is_ok()
    );
}

#[test]
fn source_open_exhaustion_preserves_original_registers_session_and_clock() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&allocation_image())
        .expect("actual original coroutine");
    machine
        .sessions
        .open_with_sid(
            usize::MAX - 2,
            vec!["A".into()],
            &BufferConfig::default(),
            &BTreeMap::from([("A".into(), LocalTypeR::End)]),
        )
        .expect("original high-water advance");
    machine.next_session_id = machine.sessions.next_session_id();
    let roles = ["A".to_string()];
    let types = [("A".to_string(), LocalTypeR::End)];
    let dsts = [("A".to_string(), 0)];
    let pack = machine
        .step_open(0, "A", &roles, &types, &[], &dsts)
        .expect("last fresh source open");
    assert!(
        matches!(pack.events.as_slice(), [ObsEvent::Opened { session, .. }] if *session == usize::MAX - 1)
    );
    let before = crate::serialization::binary_encode(&machine).unwrap();
    let error = match machine.step_open(0, "A", &roles, &types, &[], &dsts) {
        Err(error) => error,
        Ok(_) => panic!("exhausted source open must refuse"),
    };
    assert_eq!(
        error,
        Fault::SessionAllocation {
            error: crate::session::SessionAllocationError::Exhausted
        }
    );
    let encoded =
        crate::serialization::binary_encode(&error).expect("actual typed allocation fault");
    let decoded: Fault =
        crate::serialization::binary_decode(&encoded).expect("retained typed allocation fault");
    assert_eq!(decoded, error);
    assert_eq!(
        crate::faults::classify_fault(&error),
        crate::faults::FaultClass::Close
    );
    assert_eq!(
        crate::serialization::binary_encode(&machine).unwrap(),
        before
    );
}
