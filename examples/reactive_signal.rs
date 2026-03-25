//! Reactive signal example using generated algebraic effect interfaces.
//!
//! This is an effect-boundary example: `tell!` defines the signal-facing
//! capability surface, and host Rust implements the reactive state store,
//! subscription table, and notification behavior through the generated
//! `SignalRuntime` trait.

use std::collections::BTreeMap;
use telltale::tell;

tell! {
    -- // Execution profile metadata is part of the generated proof-status surface.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Effect-domain data for one signal update request.
    type alias SignalUpdate =
    {
      signalName : String
      nextValue : Int
      publisher : Role
    }

    -- // Effect-domain data for the current state of one signal.
    type alias SignalSnapshot =
    {
      signalName : String
      value : Int
      version : Int
    }

    -- // Effect-domain data for one subscription registration.
    type alias SignalSubscription =
    {
      signalName : String
      subscriber : Role
    }

    -- // Effect-domain data for one delivered notification.
    type alias SignalNotification =
    {
      subscriber : Role
      snapshot : SignalSnapshot
    }

    -- // Reactive signal runtime boundary.
    effect SignalRuntime
      command subscribe : SignalSubscription -> Unit
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }
      observe current : String -> Maybe SignalSnapshot
      {
        class : observational
        progress : immediate
        region : session
        agreement_use : forbidden
        reentrancy : allow
      }
      command publish : SignalUpdate -> SignalSnapshot
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }
      observe notify : SignalNotification -> Unit
      {
        class : observational
        progress : immediate
        region : session
        agreement_use : forbidden
        reentrancy : allow
      }

    -- // Minimal protocol showing that one publisher update becomes one observer-visible change.
    protocol ReactiveSignal uses SignalRuntime under Replay =
      roles Publisher, Reactor, Observer
      Publisher -> Reactor : PublishRequested
      Reactor -> Observer : SignalChanged
}

use ReactiveSignal::effects;

#[derive(Default)]
struct SignalHost {
    snapshots: BTreeMap<String, effects::SignalSnapshot>,
    subscriptions: Vec<effects::SignalSubscription>,
    delivered: Vec<effects::SignalNotification>,
}

impl effects::SignalRuntime for SignalHost {
    fn subscribe(&mut self, input: effects::SignalSubscription) {
        self.subscriptions.push(input);
    }

    fn current(&mut self, input: String) -> Option<effects::SignalSnapshot> {
        self.snapshots.get(&input).cloned()
    }

    fn publish(&mut self, input: effects::SignalUpdate) -> effects::SignalSnapshot {
        let next_version = self
            .snapshots
            .get(&input.signal_name)
            .map_or(1_i64, |existing| existing.version + 1);

        let snapshot = effects::SignalSnapshot {
            signal_name: input.signal_name.clone(),
            value: input.next_value,
            version: next_version,
        };
        self.snapshots
            .insert(input.signal_name.clone(), snapshot.clone());
        snapshot
    }

    fn notify(&mut self, input: effects::SignalNotification) {
        self.delivered.push(input);
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut host = SignalHost::default();
    let signal_name = "temperature".to_string();

    println!(
        "strongest tier = {}",
        ReactiveSignal::proof_status::STRONGEST_TIER
    );
    println!(
        "execution profiles = {:?}",
        ReactiveSignal::proof_status::EXECUTION_PROFILES
    );

    effects::SignalRuntime::subscribe(
        &mut host,
        effects::SignalSubscription {
            signal_name: signal_name.clone(),
            subscriber: effects::Role::new("Observer"),
        },
    );

    let before = effects::SignalRuntime::current(&mut host, signal_name.clone());
    assert!(before.is_none());

    let snapshot = effects::SignalRuntime::publish(
        &mut host,
        effects::SignalUpdate {
            signal_name: signal_name.clone(),
            next_value: 21,
            publisher: effects::Role::new("Publisher"),
        },
    );

    let subscriptions = host.subscriptions.clone();
    for subscription in subscriptions {
        effects::SignalRuntime::notify(
            &mut host,
            effects::SignalNotification {
                subscriber: subscription.subscriber,
                snapshot: snapshot.clone(),
            },
        );
    }

    let after = match effects::SignalRuntime::handle(
        &mut host,
        effects::SignalRuntimeRequest::Current(signal_name.clone()),
    ) {
        effects::SignalRuntimeOutcome::Current(current) => current,
        _ => unreachable!("current must produce the matching outcome variant"),
    };

    let current = after.ok_or("published signal must now be observable")?;

    println!("signal = {}", current.signal_name);
    println!("value = {}", current.value);
    println!("version = {}", current.version);
    println!("subscribers = {}", host.subscriptions.len());
    println!("notifications = {}", host.delivered.len());

    assert_eq!(current.signal_name, signal_name);
    assert_eq!(current.value, 21);
    assert_eq!(current.version, 1);
    assert_eq!(host.delivered.len(), 1);
    assert_eq!(host.delivered[0].subscriber.0, "Observer");

    Ok(())
}
