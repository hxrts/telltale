#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::collections::BTreeMap;

use telltale_types::{GlobalType, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::RunStatus;
use telltale_vm::{Instr, VMConfig, VM};

struct BenchHandler;

impl EffectHandler for BenchHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels to choose from".to_string())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
    }
}

fn yield_image(num_roles: usize, yields_per_role: usize) -> CodeImage {
    let mut programs = BTreeMap::new();
    let mut local_types = BTreeMap::new();

    for idx in 0..num_roles {
        let role = format!("R{idx}");
        let mut code = Vec::with_capacity(yields_per_role + 1);
        for _ in 0..yields_per_role {
            code.push(Instr::Yield);
        }
        code.push(Instr::Halt);

        programs.insert(role.clone(), code);
        local_types.insert(role, LocalTypeR::End);
    }

    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

fn bench_vm_run(c: &mut Criterion) {
    let handler = BenchHandler;
    let image_small = yield_image(8, 64);
    let image_wide = yield_image(32, 32);

    c.bench_function("vm_run_yield_small", |b| {
        b.iter(|| {
            let mut vm = VM::new(VMConfig::default());
            vm.load_choreography(black_box(&image_small))
                .expect("load choreography");
            let status = vm.run(&handler, 10_000).expect("run vm");
            assert!(matches!(status, RunStatus::AllDone));
            black_box(vm.trace().len());
        })
    });

    c.bench_function("vm_run_yield_wide", |b| {
        b.iter(|| {
            let mut vm = VM::new(VMConfig::default());
            vm.load_choreography(black_box(&image_wide))
                .expect("load choreography");
            let status = vm.run(&handler, 20_000).expect("run vm");
            assert!(matches!(status, RunStatus::AllDone));
            black_box(vm.trace().len());
        })
    });
}

criterion_group!(benches, bench_vm_run);
criterion_main!(benches);
