#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Performance benchmarks for enhanced choreography features
//!
//! This benchmark suite measures the performance impact of new features:
//! - Module (namespace) processing overhead
//! - Dynamic role projection performance
//! - Code generation with enhanced features

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use telltale_choreography::{
    ast::{LocalType, Role},
    compiler::{
        codegen::{
            generate_choreography_code, generate_choreography_code_with_dynamic_roles,
            generate_dynamic_role_support,
        },
        parser::parse_choreography_str,
        projection::project,
    },
};

// Benchmark module parsing overhead
fn bench_module_parsing(c: &mut Criterion) {
    let simple_protocol = r#"
        protocol Simple =
          roles A, B
          A -> B : Message
    "#;

    let namespaced_protocol = r#"
        module test_namespace exposing (Simple)

        protocol Simple =
          roles A, B
          A -> B : Message
    "#;

    let mut group = c.benchmark_group("module_parsing");

    group.bench_with_input(
        BenchmarkId::new("without_module", "simple"),
        &simple_protocol,
        |b, protocol| b.iter(|| parse_choreography_str(black_box(protocol)).unwrap()),
    );

    group.bench_with_input(
        BenchmarkId::new("with_module", "namespaced"),
        &namespaced_protocol,
        |b, protocol| b.iter(|| parse_choreography_str(black_box(protocol)).unwrap()),
    );

    group.finish();
}

// Benchmark dynamic role projection performance
fn bench_dynamic_role_projection(c: &mut Criterion) {
    let static_protocol = r#"
        protocol StaticRoles =
          roles Leader, Worker1, Worker2, Worker3
          Leader -> Worker1 : Task
          Leader -> Worker2 : Task
          Leader -> Worker3 : Task
    "#;

    let dynamic_protocol = r#"
        protocol DynamicRoles =
          roles Leader, Workers[*]
          Leader -> Workers[*] : Task
          Workers[0..threshold] -> Leader : Response
    "#;

    let static_choreo = parse_choreography_str(static_protocol).unwrap();
    let dynamic_choreo = parse_choreography_str(dynamic_protocol).unwrap();

    let mut group = c.benchmark_group("role_projection");

    // Benchmark static role projection
    group.bench_with_input(
        BenchmarkId::new("static_roles", "projection"),
        &static_choreo,
        |b, choreo| {
            b.iter(|| {
                for role in &choreo.roles {
                    let _ = project(black_box(choreo), black_box(role));
                }
            })
        },
    );

    // Benchmark dynamic role projection (may include some failures, but measures overhead)
    group.bench_with_input(
        BenchmarkId::new("dynamic_roles", "projection"),
        &dynamic_choreo,
        |b, choreo| {
            b.iter(|| {
                for role in &choreo.roles {
                    let _ = project(black_box(choreo), black_box(role));
                }
            })
        },
    );

    group.finish();
}

// Benchmark code generation performance
fn bench_code_generation(c: &mut Criterion) {
    let static_choreo = parse_choreography_str(
        r#"
        protocol StaticProtocol =
          roles A, B, C
          A -> B : Message1
          B -> C : Message2
          C -> A : Message3
    "#,
    )
    .unwrap();

    let dynamic_choreo = parse_choreography_str(
        r#"
        protocol DynamicProtocol =
          roles Controller, Workers[*]
          Controller -> Workers[*] : Task
          Workers[0..count] -> Controller : Result
    "#,
    )
    .unwrap();

    // Create simplified local types for benchmarking
    let static_local_types: Vec<(Role, LocalType)> = static_choreo
        .roles
        .iter()
        .map(|role| (role.clone(), LocalType::End))
        .collect();

    let dynamic_local_types: Vec<(Role, LocalType)> = dynamic_choreo
        .roles
        .iter()
        .map(|role| (role.clone(), LocalType::End))
        .collect();

    let mut group = c.benchmark_group("code_generation");

    // Benchmark standard code generation
    group.bench_with_input(
        BenchmarkId::new("standard", "generation"),
        &(&static_choreo, &static_local_types),
        |b, (choreo, local_types)| {
            b.iter(|| {
                generate_choreography_code(
                    &choreo.name.to_string(),
                    black_box(&choreo.roles),
                    black_box(local_types),
                )
            })
        },
    );

    // Benchmark enhanced code generation with dynamic support
    group.bench_with_input(
        BenchmarkId::new("dynamic", "generation"),
        &(&dynamic_choreo, &dynamic_local_types),
        |b, (choreo, local_types)| {
            b.iter(|| {
                generate_choreography_code_with_dynamic_roles(
                    black_box(choreo),
                    black_box(local_types),
                )
            })
        },
    );

    // Benchmark dynamic support generation
    group.bench_function("dynamic_support_only", |b| {
        b.iter(|| generate_dynamic_role_support(black_box(&dynamic_choreo)))
    });

    group.finish();
}

// Benchmark complex protocol parsing (all features combined)
fn bench_complex_protocol(c: &mut Criterion) {
    let complex_protocol = r#"
        module performance_benchmark exposing (ComplexProtocol)

        protocol ComplexProtocol =
          roles Coordinator, Workers[*], Database, Monitor
          Coordinator -> Workers[*] : InitializeWork
          branch
            Workers[i] -> Database : DataRequest
            Database -> Workers[i] : DataResponse
          branch
            Workers[0..quorum] -> Coordinator : WorkResult
          case choose Coordinator of
            Success ->
              Coordinator -> Monitor : SuccessReport
              Coordinator -> Workers[*] : Cleanup
            Failure ->
              Coordinator -> Monitor : FailureAlert
              Coordinator -> Database : RollbackTransaction
            Retry ->
              Coordinator -> Workers[*] : RetryWork
          Monitor -> Coordinator : MonitoringComplete
    "#;

    let mut group = c.benchmark_group("complex_protocol");

    // Benchmark parsing
    group.bench_function("parse_complex", |b| {
        b.iter(|| parse_choreography_str(black_box(complex_protocol)).unwrap())
    });

    // Benchmark full pipeline
    let choreo = parse_choreography_str(complex_protocol).unwrap();
    let local_types: Vec<(Role, LocalType)> = choreo
        .roles
        .iter()
        .map(|role| (role.clone(), LocalType::End))
        .collect();

    group.bench_function("full_pipeline", |b| {
        b.iter(|| {
            let parsed = parse_choreography_str(black_box(complex_protocol)).unwrap();

            // Try projection (may fail for dynamic roles without bindings)
            for role in &parsed.roles {
                let _ = project(&parsed, role);
            }

            // Generate code
            let _ = generate_choreography_code_with_dynamic_roles(&parsed, &local_types);
        })
    });

    group.finish();
}

// Benchmark scalability with increasing protocol size
fn bench_scalability(c: &mut Criterion) {
    let mut group = c.benchmark_group("scalability");

    for size in [5, 10, 20, 50].iter() {
        let protocol = generate_large_protocol(*size);

        group.bench_with_input(BenchmarkId::new("parse", size), &protocol, |b, protocol| {
            b.iter(|| parse_choreography_str(black_box(protocol)).unwrap())
        });
    }

    group.finish();
}

// Helper function to generate large protocols for scalability testing
fn generate_large_protocol(role_count: usize) -> String {
    let mut protocol = String::from(
        "module scalability_test exposing (LargeProtocol)\n\nprotocol LargeProtocol =\n  roles ",
    );

    // Generate roles
    for i in 0..role_count {
        if i > 0 {
            protocol.push_str(", ");
        }
        protocol.push_str(&format!("Role{}", i));
    }
    protocol.push_str("\n\n");

    // Generate interactions (each role sends to the next)
    for i in 0..role_count {
        let next = (i + 1) % role_count;
        protocol.push_str(&format!("  Role{} -> Role{} : Message{}\n", i, next, i));
    }
    protocol
}

// Benchmark memory usage patterns
fn bench_memory_usage(c: &mut Criterion) {
    let complex_protocol = r#"
        module memory_test exposing (MemoryTest)

        protocol MemoryTest =
          roles A, B[*], C[N], D[5]
          A -> B[*] : LargeMessage
          B[0..subset] -> C[*] : ProcessedData
          C[i] -> D[0] : AggregatedResult
          D[0] -> A : FinalResult
    "#;

    let mut group = c.benchmark_group("memory_usage");

    // Benchmark memory allocation during parsing
    group.bench_function("parse_allocation", |b| {
        b.iter(|| {
            let _choreo = parse_choreography_str(black_box(complex_protocol)).unwrap();

            // Force allocation by parsing again since clone is no longer available
            let _cloned = parse_choreography_str(black_box(complex_protocol)).unwrap();
        })
    });

    // Benchmark projection memory usage
    let choreo = parse_choreography_str(complex_protocol).unwrap();
    group.bench_function("projection_allocation", |b| {
        b.iter(|| {
            for role in &choreo.roles {
                let _ = project(black_box(&choreo), black_box(role));
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_module_parsing,
    bench_dynamic_role_projection,
    bench_code_generation,
    bench_complex_protocol,
    bench_scalability,
    bench_memory_usage
);

criterion_main!(benches);
