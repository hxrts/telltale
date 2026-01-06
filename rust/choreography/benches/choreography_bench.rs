#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Benchmarks for choreographic programming critical paths
//
// This benchmark suite tests the performance of:
// - Projection algorithm (global choreography → local types)
// - Static analysis (role extraction, dependencies, progress checking)
// - Code generation (AST → Rust session types)
// - Effect interpretation (effect algebra execution)

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use quote::format_ident;
use rumpsteak_aura_choreography::{
    ast::{Annotations, Branch, Choreography, Condition, MessageType, NonEmptyVec, Protocol, Role},
    compiler::{codegen::generate_session_type, projection::project},
    effects::{interpret, LabelId, NoOpHandler, Program, RoleId},
    identifiers::RoleName,
};
use std::collections::HashMap;

// Helper to create roles
fn role(name: &str) -> Role {
    Role::new(format_ident!("{}", name)).unwrap()
}

// Helper to create a simple choreography for benchmarking
fn create_simple_choreography() -> Choreography {
    let alice = role("Alice");
    let bob = role("Bob");

    Choreography {
        name: format_ident!("SimpleBench"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Send {
            from: alice.clone(),
            to: bob.clone(),
            message: MessageType {
                name: format_ident!("Number"),
                type_annotation: None,
                payload: None,
            },
            annotations: Annotations::new(),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
            continuation: Box::new(Protocol::Send {
                from: bob,
                to: alice,
                message: MessageType {
                    name: format_ident!("Response"),
                    type_annotation: None,
                    payload: None,
                },
                annotations: Annotations::new(),
                from_annotations: Annotations::new(),
                to_annotations: Annotations::new(),
                continuation: Box::new(Protocol::End),
            }),
        },
        attrs: HashMap::new(),
    }
}

// Create a complex choreography with choices and loops
fn create_complex_choreography() -> Choreography {
    let alice = role("Alice");
    let bob = role("Bob");
    let charlie = role("Charlie");

    Choreography {
        name: format_ident!("ComplexBench"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), charlie.clone()],
        protocol: Protocol::Loop {
            condition: Some(Condition::Count(5)),
            body: Box::new(Protocol::Send {
                from: alice.clone(),
                to: bob.clone(),
                message: MessageType {
                    name: format_ident!("Request"),
                    type_annotation: None,
                    payload: None,
                },
                annotations: Annotations::new(),
                from_annotations: Annotations::new(),
                to_annotations: Annotations::new(),
                continuation: Box::new(Protocol::Choice {
                    role: bob.clone(),
                    annotations: Annotations::new(),
                    branches: NonEmptyVec::from_head_tail(
                        Branch {
                            label: format_ident!("Accept"),
                            guard: None,
                            protocol: Protocol::Send {
                                from: bob.clone(),
                                to: charlie.clone(),
                                message: MessageType {
                                    name: format_ident!("Data"),
                                    type_annotation: None,
                                    payload: None,
                                },
                                annotations: Annotations::new(),
                                from_annotations: Annotations::new(),
                                to_annotations: Annotations::new(),
                                continuation: Box::new(Protocol::End),
                            },
                        },
                        vec![Branch {
                            label: format_ident!("Reject"),
                            guard: None,
                            protocol: Protocol::Send {
                                from: bob.clone(),
                                to: alice.clone(),
                                message: MessageType {
                                    name: format_ident!("Error"),
                                    type_annotation: None,
                                    payload: None,
                                },
                                annotations: Annotations::new(),
                                from_annotations: Annotations::new(),
                                to_annotations: Annotations::new(),
                                continuation: Box::new(Protocol::End),
                            },
                        }],
                    ),
                }),
            }),
        },
        attrs: HashMap::new(),
    }
}

// Define a simple role type for effect programs
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
enum SimpleRole {
    Alice,
    Bob,
}

// Define a simple label type for effect programs
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
enum SimpleLabel {
    Default,
}

impl LabelId for SimpleLabel {
    fn as_str(&self) -> &'static str {
        match self {
            SimpleLabel::Default => "default",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "default" => Some(SimpleLabel::Default),
            _ => None,
        }
    }
}

impl RoleId for SimpleRole {
    type Label = SimpleLabel;

    fn role_name(&self) -> RoleName {
        match self {
            SimpleRole::Alice => RoleName::from_static("Alice"),
            SimpleRole::Bob => RoleName::from_static("Bob"),
        }
    }
}

// Create an effect program for benchmarking
fn create_effect_program() -> Program<SimpleRole, String> {
    Program::new()
        .send(SimpleRole::Bob, "hello".to_string())
        .recv::<String>(SimpleRole::Bob)
        .send(SimpleRole::Bob, "goodbye".to_string())
        .end()
}

// Benchmark projection algorithm
fn bench_projection(c: &mut Criterion) {
    let mut group = c.benchmark_group("projection");

    let simple = create_simple_choreography();
    let complex = create_complex_choreography();

    group.bench_function("simple_protocol", |b| {
        let alice = role("Alice");
        b.iter(|| project(black_box(&simple), &alice));
    });

    group.bench_function("complex_protocol", |b| {
        let alice = role("Alice");
        b.iter(|| project(black_box(&complex), &alice));
    });

    group.finish();
}

// Benchmark static analysis (using choreography validation as proxy since Analyzer is private)
fn bench_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("analysis");

    let simple = create_simple_choreography();
    let complex = create_complex_choreography();

    group.bench_function("validate_simple", |b| {
        b.iter(|| black_box(&simple).validate());
    });

    group.bench_function("validate_complex", |b| {
        b.iter(|| black_box(&complex).validate());
    });

    group.bench_function("mentions_role_simple", |b| {
        let alice = role("Alice");
        b.iter(|| black_box(&simple).protocol.mentions_role(&alice));
    });

    group.bench_function("mentions_role_complex", |b| {
        let alice = role("Alice");
        b.iter(|| black_box(&complex).protocol.mentions_role(&alice));
    });

    group.finish();
}

// Benchmark code generation
fn bench_codegen(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen");

    let simple = create_simple_choreography();
    let complex = create_complex_choreography();

    // Project first to get local types
    let alice = role("Alice");
    let simple_local = project(&simple, &alice).unwrap();
    let complex_local = project(&complex, &alice).unwrap();

    group.bench_function("generate_simple", |b| {
        b.iter(|| generate_session_type(&alice, black_box(&simple_local), "SimpleBench"));
    });

    group.bench_function("generate_complex", |b| {
        b.iter(|| generate_session_type(&alice, black_box(&complex_local), "ComplexBench"));
    });

    group.finish();
}

// Benchmark effect interpretation
fn bench_effects(c: &mut Criterion) {
    let mut group = c.benchmark_group("effects");

    group.bench_function("interpret_program", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| {
            let program = create_effect_program();
            rt.block_on(async {
                let mut handler = NoOpHandler::<SimpleRole>::new();
                let mut endpoint = ();
                interpret(&mut handler, &mut endpoint, black_box(program)).await
            })
        });
    });

    group.finish();
}

// Benchmark program validation
fn bench_validation(c: &mut Criterion) {
    let mut group = c.benchmark_group("validation");

    let simple = create_simple_choreography();
    let complex = create_complex_choreography();
    let program = create_effect_program();

    group.bench_function("validate_simple_choreography", |b| {
        b.iter(|| black_box(&simple).validate());
    });

    group.bench_function("validate_complex_choreography", |b| {
        b.iter(|| black_box(&complex).validate());
    });

    group.bench_function("validate_effect_program", |b| {
        b.iter(|| black_box(&program).validate());
    });

    group.finish();
}

// Benchmark varying choreography sizes
fn bench_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling");

    // Keep the iteration counts small so the benchmark remains fast but
    // still highlights how projection time grows with additional sends.
    for num_interactions in &[2, 4, 8, 16] {
        let alice = role("Alice");
        let bob = role("Bob");

        // Create a linear protocol with N send operations (responses are implicit in choreographies)
        let mut protocol = Protocol::End;
        for i in 0..*num_interactions {
            // Alternate sender for more interesting protocols
            let (from, to) = if i % 2 == 0 {
                (alice.clone(), bob.clone())
            } else {
                (bob.clone(), alice.clone())
            };

            protocol = Protocol::Send {
                from,
                to,
                message: MessageType {
                    name: format_ident!("Msg"),
                    type_annotation: None,
                    payload: None,
                },
                annotations: Annotations::new(),
                from_annotations: Annotations::new(),
                to_annotations: Annotations::new(),
                continuation: Box::new(protocol),
            };
        }

        let bench_name = format!("ScalingBench{num_interactions}");
        let choreography = Choreography {
            name: syn::parse_str::<syn::Ident>(&bench_name).unwrap(),
            namespace: None,
            roles: vec![alice, bob],
            protocol,
            attrs: HashMap::new(),
        };

        group.bench_with_input(
            BenchmarkId::from_parameter(num_interactions),
            &choreography,
            |b, choreo| {
                let alice = role("Alice");
                b.iter(|| project(black_box(choreo), &alice));
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_projection,
    bench_analysis,
    bench_codegen,
    bench_effects,
    bench_validation,
    bench_scaling
);

criterion_main!(benches);
