use super::*;

#[test]
fn test_can_step_head() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let act = GlobalAction::new("A", "B", Label::new("msg"));
    assert!(can_step(&g, &act));
}

#[test]
fn test_can_step_wrong_action() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let wrong = GlobalAction::new("B", "A", Label::new("msg"));
    assert!(!can_step(&g, &wrong));
}

#[test]
fn test_can_step_wrong_label() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let wrong = GlobalAction::new("A", "B", Label::new("other"));
    assert!(!can_step(&g, &wrong));
}

#[test]
fn test_can_step_wrong_sort() {
    let g = GlobalType::send(
        "A",
        "B",
        Label::with_sort("msg", telltale_types::PayloadSort::Nat),
        GlobalType::End,
    );
    let wrong = GlobalAction::new(
        "A",
        "B",
        Label::with_sort("msg", telltale_types::PayloadSort::Bool),
    );
    assert!(!can_step(&g, &wrong));
}

#[test]
fn test_can_step_async() {
    let inner = GlobalType::send("C", "D", Label::new("m2"), GlobalType::End);
    let g = GlobalType::send("A", "B", Label::new("m1"), inner);

    let act = GlobalAction::new("C", "D", Label::new("m2"));
    assert!(can_step(&g, &act));
}

#[test]
fn test_can_step_async_blocked() {
    let inner = GlobalType::send("C", "B", Label::new("m2"), GlobalType::End);
    let g = GlobalType::send("A", "B", Label::new("m1"), inner);

    let act = GlobalAction::new("C", "B", Label::new("m2"));
    assert!(!can_step(&g, &act));
}

#[test]
fn test_can_step_mu() {
    let g = GlobalType::mu(
        "t",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
    );
    let act = GlobalAction::new("A", "B", Label::new("msg"));
    assert!(can_step(&g, &act));
}

#[test]
fn test_step_head() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let act = GlobalAction::new("A", "B", Label::new("msg"));
    assert_eq!(step(&g, &act), Some(GlobalType::End));
}

#[test]
fn test_step_async() {
    let inner = GlobalType::send("C", "D", Label::new("m2"), GlobalType::End);
    let g = GlobalType::send("A", "B", Label::new("m1"), inner);

    let act = GlobalAction::new("C", "D", Label::new("m2"));
    let result = step(&g, &act);

    let expected = GlobalType::send("A", "B", Label::new("m1"), GlobalType::End);
    assert_eq!(result, Some(expected));
}

#[test]
fn test_step_mu() {
    let g = GlobalType::mu(
        "t",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
    );
    let act = GlobalAction::new("A", "B", Label::new("msg"));
    let result = step(&g, &act);
    assert_eq!(result, Some(g));
}

#[test]
fn test_local_can_step_send() {
    let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
    let act = LocalAction::send("B", Label::new("msg"));
    assert!(local_can_step(&lt, &act));
}

#[test]
fn test_local_can_step_recv() {
    let lt = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
    let act = LocalAction::recv("A", Label::new("msg"));
    assert!(local_can_step(&lt, &act));
}

#[test]
fn test_local_can_step_wrong_sort() {
    let lt = LocalTypeR::recv(
        "A",
        Label::with_sort("msg", telltale_types::PayloadSort::Nat),
        LocalTypeR::End,
    );
    let act = LocalAction::recv(
        "A",
        Label::with_sort("msg", telltale_types::PayloadSort::Bool),
    );
    assert!(!local_can_step(&lt, &act));
}

#[test]
fn test_local_can_step_async() {
    let inner = LocalTypeR::send("C", Label::new("m2"), LocalTypeR::End);
    let lt = LocalTypeR::send("B", Label::new("m1"), inner);

    let act = LocalAction::send("C", Label::new("m2"));
    assert!(local_can_step(&lt, &act));
}

#[test]
fn test_local_step_send() {
    let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
    let act = LocalAction::send("B", Label::new("msg"));
    assert_eq!(local_step(&lt, &act), Some(LocalTypeR::End));
}

#[test]
fn test_consume_with_proof() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let result = consume_with_proof(&g, "A", "B", &Label::new("msg"));

    assert!(result.is_some());
    let proof = result.expect("consume_with_proof should produce continuation");
    assert_eq!(proof.continuation(), &GlobalType::End);
}

#[test]
fn test_reduces() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    assert!(reduces(&g, &GlobalType::End));
}

#[test]
fn test_reduces_star() {
    let g1 = GlobalType::send(
        "A",
        "B",
        Label::new("m1"),
        GlobalType::send("B", "C", Label::new("m2"), GlobalType::End),
    );
    assert!(reduces_star(&g1, &GlobalType::End));
}

#[test]
fn test_good_g() {
    let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    assert!(good_g(&g));
}

#[test]
fn test_local_action_to_global() {
    let act = LocalAction::send("B", Label::new("msg"));
    let global = act.to_global("A");
    assert_eq!(global.sender, "A");
    assert_eq!(global.receiver, "B");
}

#[test]
fn test_can_step_with_deep_fuel_bound() {
    fn deep_prefix(depth: usize, tail: GlobalType) -> GlobalType {
        let mut acc = tail;
        for i in (0..depth).rev() {
            acc = GlobalType::send("A", "B", Label::new(format!("p{i}")), acc);
        }
        acc
    }

    let g = deep_prefix(150, GlobalType::send("C", "D", Label::new("target"), GlobalType::End));
    let act = GlobalAction::new("C", "D", Label::new("target"));

    assert!(!can_step_with_fuel(
        &g,
        &act,
        crate::limits::TraversalFuel(50)
    ));
    assert!(can_step_with_fuel(
        &g,
        &act,
        crate::limits::TraversalFuel(500)
    ));
}
