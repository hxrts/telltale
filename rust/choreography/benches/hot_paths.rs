#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use telltale_choreography::compiler::parser::parse_choreography_str;
use telltale_choreography::compiler::projection::project;
use telltale_choreography::effects::{interpret, Program};

fn sample_protocol() -> &'static str {
    r#"
protocol HotPath =
  roles Alice, Bob
  Alice -> Bob : M0
  Bob -> Alice : M1
  Alice -> Bob : M2
"#
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum BenchRole {
    Alice,
    Bob,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum BenchLabel {
    L0,
}

impl telltale_choreography::LabelId for BenchLabel {
    fn as_str(&self) -> &'static str {
        "L0"
    }

    fn from_str(label: &str) -> Option<Self> {
        (label == "L0").then_some(Self::L0)
    }
}

impl telltale_choreography::RoleId for BenchRole {
    type Label = BenchLabel;

    fn role_name(&self) -> telltale_choreography::RoleName {
        match self {
            Self::Alice => telltale_choreography::RoleName::from_static("Alice"),
            Self::Bob => telltale_choreography::RoleName::from_static("Bob"),
        }
    }
}

fn parser_hot_path(c: &mut Criterion) {
    let src = sample_protocol();
    c.bench_function("hot_paths.parser.parse", |b| {
        b.iter(|| parse_choreography_str(black_box(src)).expect("parse protocol"));
    });
}

fn projection_hot_path(c: &mut Criterion) {
    let choreo = parse_choreography_str(sample_protocol()).expect("parse protocol");
    let role = choreo.roles.first().expect("alice role").clone();

    c.bench_function("hot_paths.projection.alice", |b| {
        b.iter(|| project(black_box(&choreo), black_box(&role)).expect("project"));
    });
}

fn interpreter_hot_path(c: &mut Criterion) {
    let program = Program::<BenchRole, String>::new()
        .send(BenchRole::Bob, "hello".to_string())
        .recv::<String>(BenchRole::Bob)
        .send(BenchRole::Alice, "ack".to_string())
        .send(BenchRole::Bob, "bye".to_string())
        .end();

    c.bench_function("hot_paths.interpreter.noop", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().expect("tokio runtime");
            rt.block_on(async {
                let mut handler = telltale_choreography::NoOpHandler::<BenchRole>::new();
                let mut endpoint = ();
                let _ = interpret(&mut handler, &mut endpoint, black_box(program.clone())).await;
            });
        });
    });
}

criterion_group!(
    benches,
    parser_hot_path,
    projection_hot_path,
    interpreter_hot_path
);
criterion_main!(benches);
