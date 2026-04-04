//! Distributed simulation tests using nested ProtocolMachines.

use std::collections::{BTreeMap, BTreeSet};

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::semantic_objects::ProtocolMachineSemanticObjects;
use telltale_machine::trace::normalize_trace as normalize_ticks;
use telltale_machine::{
    ObsEvent, ProtocolMachine, ProtocolMachineConfig, PublicationStatus,
    SEMANTIC_OBJECTS_SCHEMA_VERSION,
};
use telltale_simulator::distributed::{DistributedSimBuilder, NestedExecutionContract};
use telltale_types::{GlobalType, Label, LocalTypeR};

struct NoOpHandler;

impl EffectHandler for NoOpHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> EffectResult<String> {
        EffectResult::success(
            labels
                .first()
                .cloned()
                .expect("labels should contain at least one branch"),
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn simple_protocol(
    sender: &str,
    receiver: &str,
    label: &str,
) -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send(sender, receiver, Label::new(label), GlobalType::End);
    let mut locals = BTreeMap::new();
    locals.insert(
        sender.to_string(),
        LocalTypeR::Send {
            partner: receiver.into(),
            branches: vec![(Label::new(label), None, LocalTypeR::End)],
        },
    );
    locals.insert(
        receiver.to_string(),
        LocalTypeR::Recv {
            partner: sender.into(),
            branches: vec![(Label::new(label), None, LocalTypeR::End)],
        },
    );
    (global, locals)
}

fn outer_loop_protocol(
    site_a: &str,
    site_b: &str,
    label: &str,
) -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::mu(
        "loop",
        GlobalType::send(
            site_a,
            site_b,
            Label::new(label),
            GlobalType::send(site_b, site_a, Label::new(label), GlobalType::var("loop")),
        ),
    );

    let mut locals = BTreeMap::new();
    locals.insert(
        site_a.to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Send {
                partner: site_b.into(),
                branches: vec![(
                    Label::new(label),
                    None,
                    LocalTypeR::Recv {
                        partner: site_b.into(),
                        branches: vec![(Label::new(label), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );
    locals.insert(
        site_b.to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Recv {
                partner: site_a.into(),
                branches: vec![(
                    Label::new(label),
                    None,
                    LocalTypeR::Send {
                        partner: site_a.into(),
                        branches: vec![(Label::new(label), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );
    (global, locals)
}

fn normalized_pairs(trace: &[ObsEvent]) -> Vec<(u64, String, String, String, String)> {
    normalize_ticks(trace)
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::Sent {
                tick,
                from,
                to,
                label,
                ..
            } => Some((
                *tick,
                "sent".into(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            ObsEvent::Received {
                tick,
                from,
                to,
                label,
                ..
            } => Some((
                *tick,
                "recv".into(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            _ => None,
        })
        .collect()
}

fn per_session(trace: &[ObsEvent], sid: usize) -> Vec<(u64, String, String, String, String)> {
    normalize_ticks(trace)
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::Sent {
                tick,
                session,
                from,
                to,
                label,
                ..
            } if *session == sid => Some((
                *tick,
                "sent".into(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            ObsEvent::Received {
                tick,
                session,
                from,
                to,
                label,
                ..
            } if *session == sid => Some((
                *tick,
                "recv".into(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            _ => None,
        })
        .collect()
}

fn assert_site_semantics(objects: &ProtocolMachineSemanticObjects) {
    assert_eq!(objects.schema_version, SEMANTIC_OBJECTS_SCHEMA_VERSION);
    assert!(
        objects.parity_critical_operations_have_progress_contracts(),
        "site semantic objects must carry progress contracts for parity-critical operations"
    );
    assert!(
        objects
            .progress_contracts
            .iter()
            .all(|contract| contract.is_terminal()),
        "distributed fixture should drive all site-local operations to terminal progress"
    );
    assert!(
        !objects.publication_events.is_empty(),
        "site semantic objects should expose canonical publications"
    );
    let publication_ids = objects
        .publication_events
        .iter()
        .map(|publication| publication.publication_id.clone())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        publication_ids.len(),
        objects.publication_events.len(),
        "site publication identifiers must remain canonical and unique"
    );
    assert!(
        objects
            .publication_events
            .iter()
            .all(|publication| match publication.status {
                PublicationStatus::Published => publication.reason.is_none(),
                PublicationStatus::Rejected => publication
                    .reason
                    .as_deref()
                    .is_some_and(|reason| reason.contains("proof-bearing success required")),
            }),
        "site publication outcomes should retain stable success/rejection diagnostics"
    );
}

#[test]
fn test_distributed_two_site() {
    let (inner_global, inner_locals) = simple_protocol("A", "B", "msg");
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);

    let (outer_global, outer_locals) = outer_loop_protocol("site_A", "site_B", "tick");
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let builder = DistributedSimBuilder::new()
        .add_site("site_A", vec![inner_image.clone()])
        .add_site("site_B", vec![inner_image])
        .inter_site(outer_image);

    let mut sim = builder
        .build_with(&ProtocolMachineConfig::default(), |_| Box::new(NoOpHandler))
        .expect("build distributed sim");

    let _report = sim.run(50).expect("run outer machine");

    assert_eq!(sim.handler().site_all_done("site_A"), Some(true));
    assert_eq!(sim.handler().site_all_done("site_B"), Some(true));

    let trace_a = sim.handler().site_trace("site_A").expect("site A trace");
    let trace_b = sim.handler().site_trace("site_B").expect("site B trace");
    assert!(
        !normalized_pairs(&trace_a).is_empty(),
        "site A should emit events"
    );
    assert!(
        !normalized_pairs(&trace_b).is_empty(),
        "site B should emit events"
    );
}

#[test]
fn distributed_simulation_exposes_nested_execution_contract() {
    let (inner_global, inner_locals) = simple_protocol("A", "B", "msg");
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);

    let (outer_global, outer_locals) = outer_loop_protocol("site_A", "site_B", "tick");
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let contract = NestedExecutionContract {
        outer_scheduler_concurrency: 3,
        inner_rounds_per_step: 2,
    };

    let simulation = DistributedSimBuilder::new()
        .add_site("site_A", vec![inner_image.clone()])
        .add_site("site_B", vec![inner_image])
        .inter_site(outer_image)
        .execution_contract(contract)
        .build(&ProtocolMachineConfig::default())
        .expect("build distributed simulation");

    assert_eq!(simulation.execution_contract(), contract);
}

#[test]
fn test_nested_matches_flat_per_site() {
    let (inner_global, inner_locals) = simple_protocol("A", "B", "msg");
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);

    let (outer_global, outer_locals) = outer_loop_protocol("site_A", "site_B", "tick");
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let builder = DistributedSimBuilder::new()
        .add_site("site_A", vec![inner_image.clone()])
        .add_site("site_B", vec![inner_image.clone()])
        .inter_site(outer_image);

    let mut sim = builder
        .build_with(&ProtocolMachineConfig::default(), |_| Box::new(NoOpHandler))
        .expect("build distributed sim");

    let _report = sim.run(50).expect("run outer machine");

    let nested_a = normalized_pairs(&sim.handler().site_trace("site_A").expect("site A trace"));
    let nested_b = normalized_pairs(&sim.handler().site_trace("site_B").expect("site B trace"));

    let mut flat = ProtocolMachine::new(ProtocolMachineConfig::default());
    let sid_a = flat.load_choreography(&inner_image).expect("load A");
    let sid_b = flat.load_choreography(&inner_image).expect("load B");

    let handler = NoOpHandler;
    flat.run_concurrent(&handler, 50, 1)
        .expect("run flat machine");

    let flat_a = per_session(flat.trace(), sid_a);
    let flat_b = per_session(flat.trace(), sid_b);

    assert_eq!(nested_a, flat_a, "site A trace should match flat session");
    assert_eq!(nested_b, flat_b, "site B trace should match flat session");
}

#[test]
fn test_distributed_concurrency_configuration() {
    let (inner_global, inner_locals) = simple_protocol("A", "B", "msg");
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);

    let (outer_global, outer_locals) = outer_loop_protocol("site_A", "site_B", "tick");
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let contract = NestedExecutionContract {
        outer_scheduler_concurrency: 2,
        inner_rounds_per_step: 3,
    };

    let builder = DistributedSimBuilder::new()
        .add_site("site_A", vec![inner_image.clone()])
        .add_site("site_B", vec![inner_image])
        .inter_site(outer_image)
        .execution_contract(contract);

    let mut sim = builder
        .build_with(&ProtocolMachineConfig::default(), |_| Box::new(NoOpHandler))
        .expect("build distributed sim");

    assert_eq!(sim.execution_contract(), contract);
    assert_eq!(sim.handler().rounds_per_step(), 3);

    let _report = sim.run(50).expect("run outer machine");
    assert_eq!(sim.handler().site_all_done("site_A"), Some(true));
    assert_eq!(sim.handler().site_all_done("site_B"), Some(true));
}

#[test]
fn nested_distributed_sites_export_semantic_objects_not_just_traces() {
    let (inner_global, inner_locals) = simple_protocol("A", "B", "msg");
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);

    let (outer_global, outer_locals) = outer_loop_protocol("site_A", "site_B", "tick");
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let builder = DistributedSimBuilder::new()
        .add_site("site_A", vec![inner_image.clone()])
        .add_site("site_B", vec![inner_image])
        .inter_site(outer_image)
        .execution_contract(NestedExecutionContract {
            outer_scheduler_concurrency: 2,
            inner_rounds_per_step: 2,
        });

    let mut sim = builder
        .build_with(&ProtocolMachineConfig::default(), |_| Box::new(NoOpHandler))
        .expect("build distributed sim");

    let _report = sim.run(50).expect("run outer machine");

    let site_a = sim
        .handler()
        .site_semantic_objects("site_A")
        .expect("site A semantic objects");
    let site_b = sim
        .handler()
        .site_semantic_objects("site_B")
        .expect("site B semantic objects");

    assert_site_semantics(&site_a);
    assert_site_semantics(&site_b);
    assert_eq!(
        site_a.operation_instances.len(),
        site_b.operation_instances.len(),
        "symmetric distributed sites should expose the same semantic object shape"
    );
}

#[test]
fn distributed_harness_replays_identical_semantic_outcomes_for_identical_inputs() {
    let (inner_global, inner_locals) = simple_protocol("A", "B", "msg");
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);

    let (outer_global, outer_locals) = outer_loop_protocol("site_A", "site_B", "tick");
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let run_once = || {
        let builder = DistributedSimBuilder::new()
            .add_site("site_A", vec![inner_image.clone()])
            .add_site("site_B", vec![inner_image.clone()])
            .inter_site(outer_image.clone())
            .execution_contract(NestedExecutionContract {
                outer_scheduler_concurrency: 2,
                inner_rounds_per_step: 2,
            });

        let mut sim = builder
            .build_with(&ProtocolMachineConfig::default(), |_| Box::new(NoOpHandler))
            .expect("build distributed sim");
        let _report = sim.run(50).expect("run outer machine");

        (
            normalized_pairs(&sim.handler().site_trace("site_A").expect("site A trace")),
            normalized_pairs(&sim.handler().site_trace("site_B").expect("site B trace")),
            sim.handler()
                .site_semantic_objects("site_A")
                .expect("site A semantic objects"),
            sim.handler()
                .site_semantic_objects("site_B")
                .expect("site B semantic objects"),
        )
    };

    let first = run_once();
    let second = run_once();

    assert_eq!(first.0, second.0, "site A traces should replay identically");
    assert_eq!(first.1, second.1, "site B traces should replay identically");
    assert_eq!(
        first.2, second.2,
        "site A semantic objects should replay identically"
    );
    assert_eq!(
        first.3, second.3,
        "site B semantic objects should replay identically"
    );
}

#[test]
fn nested_execution_contract_variation_preserves_per_site_authoritative_results() {
    let (inner_global, inner_locals) = simple_protocol("A", "B", "msg");
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);

    let (outer_global, outer_locals) = outer_loop_protocol("site_A", "site_B", "tick");
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let run_once = |contract| {
        let builder = DistributedSimBuilder::new()
            .add_site("site_A", vec![inner_image.clone()])
            .add_site("site_B", vec![inner_image.clone()])
            .inter_site(outer_image.clone())
            .execution_contract(contract);

        let mut sim = builder
            .build_with(&ProtocolMachineConfig::default(), |_| Box::new(NoOpHandler))
            .expect("build distributed sim");
        let report = sim.run(50).expect("run outer machine");

        (
            normalized_pairs(&sim.handler().site_trace("site_A").expect("site A trace")),
            normalized_pairs(&sim.handler().site_trace("site_B").expect("site B trace")),
            sim.handler()
                .site_semantic_objects("site_A")
                .expect("site A semantic objects"),
            sim.handler()
                .site_semantic_objects("site_B")
                .expect("site B semantic objects"),
            report,
        )
    };

    let serial = run_once(NestedExecutionContract {
        outer_scheduler_concurrency: 1,
        inner_rounds_per_step: 1,
    });
    let grouped = run_once(NestedExecutionContract {
        outer_scheduler_concurrency: 2,
        inner_rounds_per_step: 3,
    });

    assert_eq!(
        serial.0, grouped.0,
        "site A normalized trace must remain invariant"
    );
    assert_eq!(
        serial.1, grouped.1,
        "site B normalized trace must remain invariant"
    );
    assert_eq!(
        serial.2, grouped.2,
        "site A semantic objects must remain invariant under nested scheduling changes"
    );
    assert_eq!(
        serial.3, grouped.3,
        "site B semantic objects must remain invariant under nested scheduling changes"
    );
    assert_eq!(
        serial.4.manifest.execution_regime,
        grouped.4.manifest.execution_regime
    );
    assert_eq!(
        serial.4.manifest.theorem_profile.assumption_bundle,
        grouped.4.manifest.theorem_profile.assumption_bundle
    );
    assert_eq!(
        serial.4.manifest.theorem_profile.eligibility,
        grouped.4.manifest.theorem_profile.eligibility
    );
}

#[test]
fn distributed_run_report_aligns_manifest_and_site_results() {
    let (inner_global, inner_locals) = simple_protocol("A", "B", "msg");
    let inner_image = CodeImage::from_local_types(&inner_locals, &inner_global);
    let (outer_global, outer_locals) = outer_loop_protocol("site_A", "site_B", "tick");
    let outer_image = CodeImage::from_local_types(&outer_locals, &outer_global);

    let mut sim = DistributedSimBuilder::new()
        .add_site("site_A", vec![inner_image.clone()])
        .add_site("site_B", vec![inner_image])
        .inter_site(outer_image)
        .execution_contract(NestedExecutionContract {
            outer_scheduler_concurrency: 2,
            inner_rounds_per_step: 2,
        })
        .build_with(&ProtocolMachineConfig::default(), |_| Box::new(NoOpHandler))
        .expect("build distributed sim");

    let report = sim.run(50).expect("run outer machine");

    assert_eq!(report.manifest.sites, vec!["site_A", "site_B"]);
    assert_eq!(report.sites.len(), 2);
    assert!(
        !report.outer_obs_trace.is_empty(),
        "outer VM should emit observable events in the nested report"
    );
    let site_a = report
        .sites
        .iter()
        .find(|site| site.site == "site_A")
        .expect("site A report");
    assert_eq!(
        site_a.obs_trace,
        sim.handler().site_trace("site_A").expect("site A trace"),
        "site reports must retain the same raw observable trace exposed by the nested handler"
    );
    assert_eq!(
        site_a.semantic_objects,
        sim.handler()
            .site_semantic_objects("site_A")
            .expect("site A semantic objects"),
        "site reports must retain the same canonical semantic objects exposed by the nested handler"
    );
}
