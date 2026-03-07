#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
use telltale_choreography::compiler::parser::parse_choreography_str;
use telltale_choreography::compiler::projection::project;
use telltale_choreography::effects::{interpret, Program};

struct CountingAllocator;

static ALLOC_CALLS: AtomicUsize = AtomicUsize::new(0);

#[global_allocator]
static GLOBAL_ALLOCATOR: CountingAllocator = CountingAllocator;

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        unsafe { System.realloc(ptr, layout, new_size) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        unsafe { System.alloc_zeroed(layout) }
    }
}

fn count_allocations<F, T>(f: F) -> (T, usize)
where
    F: FnOnce() -> T,
{
    let before = ALLOC_CALLS.load(Ordering::Relaxed);
    let value = f();
    let after = ALLOC_CALLS.load(Ordering::Relaxed);
    (value, after.saturating_sub(before))
}

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
    let rt = tokio::runtime::Runtime::new().expect("tokio runtime");
    let program = Program::<BenchRole, String>::new()
        .send(BenchRole::Bob, "hello".to_string())
        .send(BenchRole::Alice, "ack".to_string())
        .send(BenchRole::Bob, "bye".to_string())
        .end();

    let loop_body = Program::<BenchRole, String>::new()
        .send(BenchRole::Bob, "loop-send".to_string())
        .choose(BenchRole::Alice, BenchLabel::L0)
        .branch(
            BenchRole::Alice,
            vec![(
                BenchLabel::L0,
                Program::new()
                    .parallel(vec![
                        Program::new().send(BenchRole::Bob, "p0".to_string()).end(),
                        Program::new()
                            .send(BenchRole::Alice, "p1".to_string())
                            .end(),
                    ])
                    .end(),
            )],
        )
        .end();
    let branch_loop_heavy = Program::<BenchRole, String>::new()
        .loop_n(8, loop_body)
        .end();

    c.bench_function("hot_paths.interpreter.noop", |b| {
        b.iter(|| {
            rt.block_on(async {
                let mut handler = telltale_choreography::NoOpHandler::<BenchRole>::new();
                let mut endpoint = ();
                drop(interpret(&mut handler, &mut endpoint, black_box(program.clone())).await);
            });
        });
    });

    eprintln!(
        "hot_paths interpreter branch_loop allocations snapshot: {}",
        count_allocations(|| {
            rt.block_on(async {
                let mut handler = telltale_choreography::NoOpHandler::<BenchRole>::new();
                let mut endpoint = ();
                interpret(
                    &mut handler,
                    &mut endpoint,
                    black_box(branch_loop_heavy.clone()),
                )
                .await
            })
        })
        .1
    );

    c.bench_function("hot_paths.interpreter.branch_loop_allocations", |b| {
        b.iter_batched(
            || branch_loop_heavy.clone(),
            |program| {
                black_box(
                    count_allocations(|| {
                        rt.block_on(async {
                            let mut handler =
                                telltale_choreography::NoOpHandler::<BenchRole>::new();
                            let mut endpoint = ();
                            interpret(&mut handler, &mut endpoint, program).await
                        })
                    })
                    .1,
                )
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(
    benches,
    parser_hot_path,
    projection_hot_path,
    interpreter_hot_path
);
criterion_main!(benches);
