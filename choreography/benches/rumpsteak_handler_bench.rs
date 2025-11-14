#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Performance benchmarks for RumpsteakHandler

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rumpsteak_aura_choreography::effects::{
    handlers::rumpsteak::{RumpsteakEndpoint, RumpsteakHandler, SimpleChannel},
    ChoreoHandler, Label,
};
use serde::{Deserialize, Serialize};
use tokio::runtime::Runtime;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum BenchRole {
    Alice,
    Bob,
}

impl rumpsteak_aura::Role for BenchRole {
    type Message = BenchMessage;

    fn seal(&mut self) {}
    fn is_sealed(&self) -> bool {
        false
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct BenchMessage {
    data: Vec<u8>,
}

impl rumpsteak_aura::Message<Box<dyn std::any::Any + Send>> for BenchMessage {
    fn upcast(msg: Box<dyn std::any::Any + Send>) -> Self {
        *msg.downcast::<BenchMessage>().unwrap()
    }

    fn downcast(self) -> Result<Box<dyn std::any::Any + Send>, Self> {
        Ok(Box::new(self))
    }
}

fn bench_send_recv_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("send_recv_throughput");

    for size in &[128, 1024, 4096, 16384, 65536] {
        group.throughput(Throughput::Bytes(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let runtime = Runtime::new().unwrap();
            b.iter(|| {
                runtime.block_on(async {
                    let mut alice_ep = RumpsteakEndpoint::new(BenchRole::Alice);
                    let mut bob_ep = RumpsteakEndpoint::new(BenchRole::Bob);

                    let (alice_ch, bob_ch) = SimpleChannel::pair();
                    alice_ep.register_channel(BenchRole::Bob, alice_ch);
                    bob_ep.register_channel(BenchRole::Alice, bob_ch);

                    let mut alice_handler = RumpsteakHandler::<BenchRole, BenchMessage>::new();
                    let mut bob_handler = RumpsteakHandler::<BenchRole, BenchMessage>::new();

                    let msg = BenchMessage {
                        data: vec![0u8; size],
                    };

                    alice_handler
                        .send(&mut alice_ep, BenchRole::Bob, black_box(&msg))
                        .await
                        .unwrap();

                    let _received: BenchMessage = bob_handler
                        .recv(&mut bob_ep, BenchRole::Alice)
                        .await
                        .unwrap();
                })
            });
        });
    }

    group.finish();
}

fn bench_choice_overhead(c: &mut Criterion) {
    c.bench_function("choice_selection", |b| {
        let runtime = Runtime::new().unwrap();
        b.iter(|| {
            runtime.block_on(async {
                let mut alice_ep = RumpsteakEndpoint::new(BenchRole::Alice);
                let mut bob_ep = RumpsteakEndpoint::new(BenchRole::Bob);

                let (alice_ch, bob_ch) = SimpleChannel::pair();
                alice_ep.register_channel(BenchRole::Bob, alice_ch);
                bob_ep.register_channel(BenchRole::Alice, bob_ch);

                let mut alice_handler = RumpsteakHandler::<BenchRole, BenchMessage>::new();
                let mut bob_handler = RumpsteakHandler::<BenchRole, BenchMessage>::new();

                let label = Label("option_a");

                alice_handler
                    .choose(&mut alice_ep, BenchRole::Bob, black_box(label))
                    .await
                    .unwrap();

                let _received_label = bob_handler
                    .offer(&mut bob_ep, BenchRole::Alice)
                    .await
                    .unwrap();
            })
        });
    });
}

fn bench_sequential_messages(c: &mut Criterion) {
    let mut group = c.benchmark_group("sequential_messages");

    for count in &[10, 50, 100] {
        group.bench_with_input(BenchmarkId::from_parameter(count), count, |b, &count| {
            let runtime = Runtime::new().unwrap();
            b.iter(|| {
                runtime.block_on(async {
                    let mut alice_ep = RumpsteakEndpoint::new(BenchRole::Alice);
                    let mut bob_ep = RumpsteakEndpoint::new(BenchRole::Bob);

                    let (alice_ch, bob_ch) = SimpleChannel::pair();
                    alice_ep.register_channel(BenchRole::Bob, alice_ch);
                    bob_ep.register_channel(BenchRole::Alice, bob_ch);

                    let mut alice_handler = RumpsteakHandler::<BenchRole, BenchMessage>::new();
                    let mut bob_handler = RumpsteakHandler::<BenchRole, BenchMessage>::new();

                    let msg = BenchMessage {
                        data: vec![0u8; 1024],
                    };

                    for _ in 0..count {
                        alice_handler
                            .send(&mut alice_ep, BenchRole::Bob, black_box(&msg))
                            .await
                            .unwrap();

                        let _received: BenchMessage = bob_handler
                            .recv(&mut bob_ep, BenchRole::Alice)
                            .await
                            .unwrap();
                    }
                })
            });
        });
    }

    group.finish();
}

fn bench_metadata_tracking_overhead(c: &mut Criterion) {
    c.bench_function("metadata_tracking", |b| {
        let runtime = Runtime::new().unwrap();
        b.iter(|| {
            runtime.block_on(async {
                let mut alice_ep = RumpsteakEndpoint::new(BenchRole::Alice);
                let mut bob_ep = RumpsteakEndpoint::new(BenchRole::Bob);

                let (alice_ch, bob_ch) = SimpleChannel::pair();
                alice_ep.register_channel(BenchRole::Bob, alice_ch);
                bob_ep.register_channel(BenchRole::Alice, bob_ch);

                let mut alice_handler = RumpsteakHandler::<BenchRole, BenchMessage>::new();
                let mut bob_handler = RumpsteakHandler::<BenchRole, BenchMessage>::new();

                let msg = BenchMessage {
                    data: vec![0u8; 1024],
                };

                alice_handler
                    .send(&mut alice_ep, BenchRole::Bob, black_box(&msg))
                    .await
                    .unwrap();

                let _ = alice_ep.get_metadata(&BenchRole::Bob);

                let _received: BenchMessage = bob_handler
                    .recv(&mut bob_ep, BenchRole::Alice)
                    .await
                    .unwrap();

                let _ = bob_ep.get_metadata(&BenchRole::Alice);
            })
        });
    });
}

criterion_group!(
    benches,
    bench_send_recv_throughput,
    bench_choice_overhead,
    bench_sequential_messages,
    bench_metadata_tracking_overhead
);
criterion_main!(benches);
