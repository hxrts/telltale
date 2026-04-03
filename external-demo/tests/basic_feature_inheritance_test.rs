use external_demo::{
    aura_effect_handlers, choreography, compile_choreography, Contentable, DefaultContentId,
};

trait RandomEffects {
    fn random_bytes(&self, len: usize) -> Vec<u8>;
}

aura_effect_handlers! {
    trait_name: RandomEffects,
    mock: {
        struct_name: MockRandomHandler,
        methods: {
            random_bytes(len: usize) -> Vec<u8> => {
                vec![0; len]
            },
        },
    },
    real: {
        struct_name: RealRandomHandler,
        methods: {
            random_bytes(len: usize) -> Vec<u8> => {
                vec![7; len]
            },
        },
    },
}

#[test]
fn external_demo_reexports_current_telltale_surface() {
    choreography! {
        protocol BasicExample =
          roles Alice, Bob
          Alice -> Bob : Ping
          Bob -> Alice : Pong
    }

    let compiled = compile_choreography(
        r#"
protocol BasicExample =
  roles Alice, Bob
  Alice -> Bob : Ping
  Bob -> Alice : Pong
"#,
    )
    .expect("compile choreography");

    let global = compiled.try_global_type().expect("global type");
    let content_id: DefaultContentId = global.content_id_default().expect("content id");
    let _roles = BasicExample::sessions::setup();

    assert_eq!(compiled.role_names(), vec!["Alice", "Bob"]);
    assert!(compiled.local_type("Alice").is_some());
    assert!(compiled.local_type("Bob").is_some());
    assert_eq!(content_id, global.content_id_default().expect("content id"));
}

#[test]
fn external_demo_macros_stay_domain_specific() {
    let mock = MockRandomHandler::new();
    let real = RealRandomHandler::new();

    assert_eq!(mock.random_bytes(4), vec![0, 0, 0, 0]);
    assert_eq!(real.random_bytes(3), vec![7, 7, 7]);
}
