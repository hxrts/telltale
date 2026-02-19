//! Distributed simulation tests using nested VMs.

use std::collections::BTreeMap;

use telltale_simulator::distributed::DistributedSimBuilder;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::trace::normalize_trace as normalize_ticks;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

struct NoOpHandler;

impl EffectHandler for NoOpHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Unit)
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
            .ok_or_else(|| "no labels available".into())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
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
        .build_with(&VMConfig::default(), |_| Box::new(NoOpHandler))
        .expect("build distributed sim");

    sim.run(50).expect("run outer vm");

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
        .build_with(&VMConfig::default(), |_| Box::new(NoOpHandler))
        .expect("build distributed sim");

    sim.run(50).expect("run outer vm");

    let nested_a = normalized_pairs(&sim.handler().site_trace("site_A").expect("site A trace"));
    let nested_b = normalized_pairs(&sim.handler().site_trace("site_B").expect("site B trace"));

    let mut flat = VM::new(VMConfig::default());
    let sid_a = flat.load_choreography(&inner_image).expect("load A");
    let sid_b = flat.load_choreography(&inner_image).expect("load B");

    let handler = NoOpHandler;
    flat.run_concurrent(&handler, 50, 1).expect("run flat vm");

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

    let builder = DistributedSimBuilder::new()
        .add_site("site_A", vec![inner_image.clone()])
        .add_site("site_B", vec![inner_image])
        .inter_site(outer_image)
        .outer_concurrency(2)
        .inner_rounds_per_step(3);

    let mut sim = builder
        .build_with(&VMConfig::default(), |_| Box::new(NoOpHandler))
        .expect("build distributed sim");

    assert_eq!(sim.outer_concurrency(), 2);
    assert_eq!(sim.handler().rounds_per_step(), 3);

    sim.run(50).expect("run outer vm");
    assert_eq!(sim.handler().site_all_done("site_A"), Some(true));
    assert_eq!(sim.handler().site_all_done("site_B"), Some(true));
}
