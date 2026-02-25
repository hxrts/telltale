
#[allow(clippy::too_many_lines)]
fn step_offer(
    coro: &mut Coroutine,
    session: &mut SessionState,
    role: &str,
    chan: u16,
    label: &str,
    ctx: &ThreadedStepCtx<'_>,
) -> Result<StepPack, Fault> {
    let ep = endpoint_from_reg(coro, chan)?;
    if !coro.owned_endpoints.contains(&ep) {
        return Err(Fault::ChannelClosed {
            endpoint: ep.clone(),
        });
    }
    let sid = ep.sid;

    let local_type = session
        .local_types
        .get(&ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    match &local_type {
        LocalTypeR::Send {
            partner, branches, ..
        } => {
            let partner = partner.clone();
            let branches = branches.clone();

            let (_lbl, expected_type, continuation) = branches
                .iter()
                .find(|(l, _, _)| l.name == label)
                .ok_or_else(|| Fault::UnknownLabel {
                    label: label.to_string(),
                })?
                .clone();

            let offer_payload = Value::Str(label.to_string());
            let fast_path =
                SendDecisionFastPathInput::new(sid, role, &partner, label, Some(&offer_payload));
            let decision = if let Some(decision) =
                ctx.handler
                    .send_decision_fast_path(fast_path, &coro.regs, Some(&offer_payload))
            {
                decision.map_err(|e| Fault::Invoke { message: e })?
            } else {
                ctx.handler
                    .send_decision(SendDecisionInput {
                        sid,
                        role,
                        partner: &partner,
                        label,
                        state: &coro.regs,
                        payload: Some(offer_payload),
                    })
                    .map_err(|e| Fault::Invoke { message: e })?
            };
            if let SendDecision::Deliver(payload) = &decision {
                validate_payload(
                    ctx.config,
                    role,
                    "offer",
                    label,
                    expected_type.as_ref(),
                    payload,
                    false,
                )?;
            }
            let enqueue = match decision {
                SendDecision::Deliver(payload) => session
                    .send(role, &partner, payload)
                    .map_err(|e| Fault::Invoke { message: e })?,
                SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
            };
            match enqueue {
                EnqueueResult::Ok => {}
                EnqueueResult::WouldBlock => {
                    return Ok(StepPack {
                        coro_update: CoroUpdate::Block(BlockReason::Send {
                            edge: Edge::new(sid, role.to_string(), partner.clone()),
                        }),
                        type_update: None,
                        events: vec![],
                    });
                }
                EnqueueResult::Full => {
                    return Err(Fault::BufferFull {
                        endpoint: ep.clone(),
                    });
                }
                EnqueueResult::Dropped => {}
            }

            let original = session
                .local_types
                .get(&ep)
                .map(|entry| &entry.original)
                .unwrap_or(&LocalTypeR::End);
            let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePc,
                type_update,
                events: vec![
                    ObsEvent::Sent {
                        tick: ctx.tick,
                        edge: Edge::new(sid, role.to_string(), partner.clone()),
                        session: sid,
                        from: role.to_string(),
                        to: partner.clone(),
                        label: label.to_string(),
                    },
                    ObsEvent::Offered {
                        tick: ctx.tick,
                        edge: Edge::new(sid, role.to_string(), partner),
                        label: label.to_string(),
                    },
                ],
            })
        }
        other => Err(Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: Offer expects Send, got {other:?}"),
        }),
    }
}

fn step_close(
    session: &mut SessionState,
    ep: &Endpoint,
    sid: SessionId,
    tick: u64,
) -> Result<StepPack, Fault> {
    session.status = SessionStatus::Closed;
    session.buffers.clear();
    session.edge_traces.clear();
    session.epoch = session.epoch.saturating_add(1);

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: Some((ep.clone(), TypeUpdate::Remove)),
        events: vec![
            ObsEvent::Closed { tick, session: sid },
            ObsEvent::EpochAdvanced {
                tick,
                sid,
                epoch: session.epoch,
            },
        ],
    })
}

fn step_open(
    coro: &mut Coroutine,
    _role: &str,
    store: &ThreadedSessionStore,
    buffer_config: &BufferConfig,
    roles: &[String],
    local_types: &[(String, LocalTypeR)],
    handlers: &[((String, String), String)],
    dsts: &[(String, u16)],
    tick: u64,
) -> Result<StepPack, Fault> {
    if local_types.len() != dsts.len() {
        return Err(Fault::Close {
            message: "open arity mismatch".to_string(),
        });
    }

    let triples: Vec<(String, LocalTypeR, u16)> = local_types
        .iter()
        .zip(dsts.iter())
        .map(|((r, lt), (r2, dst))| (r.clone(), lt.clone(), r2.clone(), *dst))
        .map(|(r, lt, r2, dst)| {
            if r == r2 {
                Ok((r, lt, dst))
            } else {
                Err(Fault::Close {
                    message: "open arity mismatch".to_string(),
                })
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    let open_roles: Vec<String> = triples.iter().map(|(r, _, _)| r.clone()).collect();
    let mut distinct = BTreeSet::new();
    let spatial_ok =
        !open_roles.is_empty() && open_roles.iter().all(|r| distinct.insert(r.clone()));
    if !spatial_ok {
        return Err(Fault::Speculation {
            message: "spatial requirements failed".to_string(),
        });
    }

    let has_handler = |sender: &str, receiver: &str| {
        handlers
            .iter()
            .any(|((s, r), _)| s == sender && r == receiver)
    };
    let covers_edges = open_roles.iter().all(|sender| {
        open_roles
            .iter()
            .all(|receiver| has_handler(sender, receiver))
    });
    if !covers_edges {
        return Err(Fault::Speculation {
            message: "handler bindings missing".to_string(),
        });
    }

    let initial_types: BTreeMap<String, LocalTypeR> = local_types.iter().cloned().collect();
    let sid = store.open(open_roles.clone(), buffer_config, &initial_types);
    let session = store.get(sid).ok_or_else(|| Fault::Close {
        message: "open session missing after allocation".to_string(),
    })?;
    {
        let mut session_guard = session.lock().expect("session lock poisoned");
        for ((sender, receiver), handler_id) in handlers {
            session_guard.edge_handlers.insert(
                Edge::new(sid, sender.clone(), receiver.clone()),
                handler_id.clone(),
            );
        }
    }

    for (_, _, reg) in &triples {
        if usize::from(*reg) >= coro.regs.len() {
            return Err(Fault::OutOfRegisters);
        }
    }
    for (endpoint_role, _, reg) in &triples {
        let ep = Endpoint {
            sid,
            role: endpoint_role.clone(),
        };
        coro.regs[usize::from(*reg)] = Value::Endpoint(ep.clone());
        if !coro.owned_endpoints.contains(&ep) {
            coro.owned_endpoints.push(ep);
        }
    }

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Opened {
            tick,
            session: sid,
            roles: if roles.is_empty() {
                open_roles
            } else {
                roles.to_vec()
            },
        }],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::buffer::BufferConfig;
    use crate::coroutine::KnowledgeFact;
    use crate::effect::{EffectHandler, SendDecision, SendDecisionInput};
    use crate::verification::{Hash, Signature, VerifyingKey};
    use crate::vm::{FlowPolicy, FlowPredicate};
    use std::collections::{BTreeMap, BTreeSet};
    use telltale_types::{GlobalType, Label, LocalTypeR};

    #[derive(Debug, Clone, Copy)]
    struct NoopHandler;

    impl EffectHandler for NoopHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Unit)
        }

        fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
            Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    fn evaluate_check(
        policy: FlowPolicy,
        known_fact: &str,
        query_fact: &str,
        target: &str,
    ) -> bool {
        let mut coro = Coroutine::new(0, 0, 1, "A".to_string(), 8, usize::MAX);
        let ep = Endpoint {
            sid: 1,
            role: "A".to_string(),
        };
        coro.knowledge_set.push(crate::coroutine::KnowledgeFact {
            endpoint: ep.clone(),
            fact: known_fact.to_string(),
        });
        coro.regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep)),
            Box::new(Value::Str(query_fact.to_string())),
        );
        coro.regs[3] = Value::Str(target.to_string());

        let cfg = VMConfig {
            flow_policy: policy,
            ..VMConfig::default()
        };
        let pack = step_check(&mut coro, &cfg, "A", 2, 3, 4, 0).expect("check should execute");
        match pack.coro_update {
            CoroUpdate::AdvancePcWriteReg { val, .. } => matches!(val, Value::Bool(true)),
            _ => panic!("unexpected check update"),
        }
    }

    #[test]
    fn flow_policy_variant_matrix_for_threaded_check() {
        let mut allow_roles = BTreeSet::new();
        allow_roles.insert("Observer".to_string());

        let mut deny_roles = BTreeSet::new();
        deny_roles.insert("Observer".to_string());

        assert!(evaluate_check(
            FlowPolicy::AllowAll,
            "secret",
            "secret",
            "Observer"
        ));
        assert!(!evaluate_check(
            FlowPolicy::DenyAll,
            "secret",
            "secret",
            "Observer"
        ));
        assert!(evaluate_check(
            FlowPolicy::AllowRoles(allow_roles),
            "secret",
            "secret",
            "Observer"
        ));
        assert!(!evaluate_check(
            FlowPolicy::DenyRoles(deny_roles),
            "secret",
            "secret",
            "Observer"
        ));
        assert!(evaluate_check(
            FlowPolicy::PredicateExpr(FlowPredicate::FactContains("secret".to_string())),
            "top_secret",
            "top_secret",
            "Observer"
        ));
        assert!(evaluate_check(
            FlowPolicy::predicate(|knowledge: &KnowledgeFact, target: &str| {
                knowledge.fact.contains("secret") && target == "Observer"
            }),
            "top_secret",
            "top_secret",
            "Observer"
        ));
        let mut allow_only_observer = BTreeSet::new();
        allow_only_observer.insert("Observer".to_string());
        assert!(!evaluate_check(
            FlowPolicy::AllowRoles(allow_only_observer),
            "secret",
            "secret",
            "Blocked"
        ));
    }

    #[test]
    fn threaded_open_uses_configured_buffer_capacity() {
        let mut coro = Coroutine::new(0, 0, 0, "A".to_string(), 8, usize::MAX);
        let store = ThreadedSessionStore::new();
        let handlers = vec![
            (("A".to_string(), "A".to_string()), "hAA".to_string()),
            (("A".to_string(), "B".to_string()), "hAB".to_string()),
            (("B".to_string(), "A".to_string()), "hBA".to_string()),
            (("B".to_string(), "B".to_string()), "hBB".to_string()),
        ];
        let cfg = BufferConfig {
            mode: crate::buffer::BufferMode::Fifo,
            initial_capacity: 1,
            policy: crate::buffer::BackpressurePolicy::Error,
        };
        let pack = step_open(
            &mut coro,
            "A",
            &store,
            &cfg,
            &["A".to_string(), "B".to_string()],
            &[
                ("A".to_string(), LocalTypeR::End),
                ("B".to_string(), LocalTypeR::End),
            ],
            &handlers,
            &[("A".to_string(), 1), ("B".to_string(), 2)],
            1,
        )
        .expect("open should succeed");
        let sid = match pack.events.first() {
            Some(ObsEvent::Opened { session, .. }) => *session,
            other => panic!("expected opened event, got {other:?}"),
        };
        let session = store.get(sid).expect("session exists");
        let guard = session.lock().expect("session lock poisoned");
        for buffer in guard.buffers.values() {
            assert_eq!(buffer.capacity(), 1);
        }
    }

    #[test]
    fn threaded_run_reports_max_rounds_exhaustion_status() {
        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), vec![Instr::Jump { target: 0 }]);
                m
            },
            global_type: GlobalType::End,
            local_types: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), LocalTypeR::End);
                m
            },
        };
        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 1);
        vm.load_choreography(&image).expect("load choreography");
        let status = vm
            .run(&NoopHandler, 8)
            .expect("run should return bounded status");
        assert_eq!(status, RunStatus::MaxRoundsExceeded);
    }

    #[test]
    fn threaded_recv_reports_verification_fault_for_tampered_signature() {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
        );

        let store = ThreadedSessionStore::new();
        let sid = store.open(
            vec!["A".to_string(), "B".to_string()],
            &BufferConfig::default(),
            &local_types,
        );
        {
            let session = store.get(sid).expect("session exists");
            let mut session = session.lock().expect("session lock poisoned");
            let tampered = crate::buffer::SignedValue {
                payload: Value::Nat(9),
                signature: Signature {
                    signer: VerifyingKey([0_u8; 32]),
                    digest: Hash([7_u8; 32]),
                },
            };
            session
                .send_signed("A", "B", &tampered)
                .expect("inject signed payload");
        }
        let session = store.get(sid).expect("session exists");

        let mut coro = Coroutine::new(0, 0, sid, "B".to_string(), 8, usize::MAX);
        let endpoint = Endpoint {
            sid,
            role: "B".to_string(),
        };
        coro.owned_endpoints.push(endpoint.clone());
        coro.regs[0] = Value::Endpoint(endpoint);

        let config = VMConfig::default();
        let guard_resources = Arc::new(Mutex::new(BTreeMap::new()));
        let resource_states = Arc::new(Mutex::new(BTreeMap::new()));
        let crashed_sites = BTreeSet::new();
        let partitioned_edges = BTreeSet::new();
        let corrupted_edges = BTreeMap::new();
        let timed_out_sites = BTreeMap::new();
        let step_ctx = ThreadedStepCtx {
            config: &config,
            guard_resources: &guard_resources,
            resource_states: &resource_states,
            crashed_sites: &crashed_sites,
            partitioned_edges: &partitioned_edges,
            corrupted_edges: &corrupted_edges,
            timed_out_sites: &timed_out_sites,
            handler: &NoopHandler,
            tick: 1,
        };
        let err = match step_recv(&mut coro, &session, "B", 0, 1, &step_ctx) {
            Ok(_) => panic!("tampered signature must fault"),
            Err(err) => err,
        };
        assert!(matches!(err, Fault::VerificationFailed { .. }));
    }

    #[test]
    fn delegation_handoff_guard_rejects_ambiguous_endpoint_ownership() {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
        );
        let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 2);
        let sid = vm.load_choreography(&image).expect("load choreography");
        let endpoint = Endpoint {
            sid,
            role: "A".to_string(),
        };

        let mut source = None;
        let mut target = None;
        for coro in &vm.coroutines {
            let guard = coro.lock().expect("coroutine lock poisoned");
            if guard.role == "A" {
                source = Some(guard.id);
            } else if guard.role == "B" {
                target = Some(guard.id);
            }
        }
        let source = source.expect("source coroutine");
        let target = target.expect("target coroutine");
        {
            let target_arc = vm
                .coroutines
                .get(target)
                .cloned()
                .expect("target coroutine arc");
            let mut target_guard = target_arc.lock().expect("coroutine lock poisoned");
            target_guard.owned_endpoints.push(endpoint.clone());
        }

        let err = vm
            .enqueue_handoff(endpoint, source, target, vm.clock.tick)
            .expect_err("ambiguous ownership must fail");
        match err {
            Fault::Transfer { message } => {
                assert!(
                    message.contains("delegation guard violation"),
                    "unexpected transfer fault message: {message}"
                );
            }
            other => panic!("expected transfer fault, got {other:?}"),
        }
    }
}
