use super::*;

#[test]
fn test_parse_mean_field_scenario() {
    // Note: FixedQ32 values must be quoted strings in TOML for deterministic parsing
    let toml = r#"
            name = "mean_field_ising"
            roles = ["A", "B"]
            steps = 1000
            seed = 42

            [material]
            layer = "mean_field"

            [material.params]
            beta = "1.5"
            species = ["up", "down"]
            initial_state = ["0.6", "0.4"]
            step_size = "0.01"

            [output]
            format = "jsonl"
        "#;

    let scenario = Scenario::parse(toml).expect("parse scenario");
    assert_eq!(scenario.name, "mean_field_ising");
    assert_eq!(scenario.roles, vec!["A", "B"]);
    assert_eq!(scenario.steps, 1000);
    assert_eq!(scenario.seed, 42);
    match &scenario.material {
        MaterialParams::MeanField(mf) => {
            let expected = FixedQ32::from_ratio(3, 2).expect("1.5");
            let eps = FixedQ32::from_ratio(1, 1_000_000).expect("epsilon");
            assert!((mf.beta - expected).abs() < eps);
        }
        _ => panic!("expected MeanField"),
    }
}

#[test]
fn test_default_seed_when_missing() {
    // Note: FixedQ32 values must be quoted strings in TOML for deterministic parsing
    let toml = r#"
            name = "default_seed"
            roles = ["A", "B"]
            steps = 1

            [material]
            layer = "mean_field"

            [material.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"
        "#;

    let scenario = Scenario::parse(toml).expect("parse scenario");
    assert_eq!(scenario.seed, 0);
}

#[test]
fn test_parse_network_link_topology() {
    let toml = r#"
            name = "links"
            roles = ["A", "B", "C"]
            steps = 10

            [material]
            layer = "mean_field"

            [material.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"

            [network]
            base_latency_ms = 5
            latency_variance = "0.1"
            loss_probability = "0.01"

            [[network.links]]
            from = "A"
            to = "B"
            start_tick = 3
            end_tick = 9
            enabled = true
            base_latency_ms = 25
            latency_variance = "0.2"
            loss_probability = "0.4"

            [[network.links]]
            from = "B"
            to = "C"
            enabled = false
        "#;

    let scenario = Scenario::parse(toml).expect("parse scenario");
    let cfg = scenario.network_config().expect("network config");
    assert_eq!(cfg.links.len(), 2);

    let ab = &cfg.links[0];
    assert_eq!(ab.from, "A");
    assert_eq!(ab.to, "B");
    assert_eq!(ab.start_tick, Some(3));
    assert_eq!(ab.end_tick, Some(9));
    assert!(ab.enabled);
    assert_eq!(ab.base_latency, Some(Duration::from_millis(25)));
    let expected_loss = FixedQ32::from_ratio(2, 5).expect("0.4");
    let eps = FixedQ32::from_ratio(1, 1_000_000).expect("epsilon");
    assert!(
        (ab.loss_probability.expect("loss") - expected_loss).abs() < eps,
        "expected 0.4 link loss override"
    );

    let bc = &cfg.links[1];
    assert_eq!(bc.from, "B");
    assert_eq!(bc.to, "C");
    assert!(!bc.enabled);
    assert_eq!(bc.start_tick, None);
    assert_eq!(bc.end_tick, None);
}

#[test]
fn test_reject_duplicate_roles() {
    let toml = r#"
            name = "dup_roles"
            roles = ["A", "A"]
            steps = 1

            [material]
            layer = "mean_field"

            [material.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"
        "#;

    let error = Scenario::parse(toml).expect_err("duplicate roles must fail");
    assert!(error.contains("duplicate role"));
}

#[test]
fn test_reject_zero_concurrency() {
    let toml = r#"
            name = "bad_concurrency"
            roles = ["A", "B"]
            steps = 1
            concurrency = 0

            [material]
            layer = "mean_field"

            [material.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"
        "#;

    let error = Scenario::parse(toml).expect_err("zero concurrency must fail");
    assert!(error.contains("concurrency"));
}

#[test]
fn test_reject_unknown_link_role() {
    let toml = r#"
            name = "bad_link_role"
            roles = ["A", "B"]
            steps = 1

            [material]
            layer = "mean_field"

            [material.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"

            [network]
            base_latency_ms = 1

            [[network.links]]
            from = "A"
            to = "C"
            enabled = true
        "#;

    let error = Scenario::parse(toml).expect_err("unknown link role must fail");
    assert!(error.contains("unknown to-role"));
}
