#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, Criterion};

use telltale_theory::projection::{project_all, MemoizedProjector};
use telltale_theory::{
    async_subtype, check_coherent, reduces_star_with_fuel, sync_subtype, TraversalFuel,
};
use telltale_types::{GlobalType, Label, LocalTypeR};

fn chain_global(depth: usize) -> GlobalType {
    let mut g = GlobalType::End;
    for idx in (0..depth).rev() {
        g = GlobalType::send("A", "B", Label::new(format!("m{idx}")), g);
    }
    g
}

fn chain_local(depth: usize) -> LocalTypeR {
    let mut lt = LocalTypeR::End;
    for idx in (0..depth).rev() {
        lt = LocalTypeR::send("B", Label::new(format!("l{idx}")), lt);
    }
    lt
}

fn bench_projection(c: &mut Criterion) {
    let global = chain_global(128);

    c.bench_function("projection_project_all_depth_128", |b| {
        b.iter(|| {
            let result = project_all(black_box(&global)).expect("projection succeeds");
            black_box(result.len());
        })
    });

    c.bench_function("projection_memoized_hits_depth_128", |b| {
        let mut projector = MemoizedProjector::new();
        projector
            .project_shared(&global, "A")
            .expect("warm cache projection");
        b.iter(|| {
            let local = projector
                .project_shared(black_box(&global), "A")
                .expect("memoized projection");
            black_box(local);
        })
    });
}

fn bench_subtyping(c: &mut Criterion) {
    let sub = chain_local(96);
    let sup = chain_local(96);

    c.bench_function("subtyping_sync_depth_96", |b| {
        b.iter(|| {
            sync_subtype(black_box(&sub), black_box(&sup)).expect("sync subtype");
        })
    });

    c.bench_function("subtyping_async_depth_96", |b| {
        b.iter(|| {
            async_subtype(black_box(&sub), black_box(&sup)).expect("async subtype");
        })
    });
}

fn bench_coherence_and_reduction(c: &mut Criterion) {
    let global = chain_global(128);

    c.bench_function("coherence_check_depth_128", |b| {
        b.iter(|| {
            let bundle = check_coherent(black_box(&global));
            black_box(bundle.is_coherent());
        })
    });

    c.bench_function("reduction_star_depth_128", |b| {
        b.iter(|| {
            let ok = reduces_star_with_fuel(
                black_box(&global),
                black_box(&GlobalType::End),
                TraversalFuel(20_000),
            );
            black_box(ok);
        })
    });
}

criterion_group!(
    benches,
    bench_projection,
    bench_subtyping,
    bench_coherence_and_reduction
);
criterion_main!(benches);
