//! Guardrail: commit-owned VM state must be mutated only in `commit_pack`.
//!
//! This check is intentionally source-based. It protects the canonical VM
//! execution structure from accidental regressions where per-instruction step
//! functions directly mutate session type state, trace, or control-state fields.

use wasm_bindgen_test::wasm_bindgen_test;

fn between<'a>(src: &'a str, start: &str, end: &str) -> &'a str {
    let start_idx = src.find(start).expect("start marker must exist");
    let end_idx = src.find(end).expect("end marker must exist");
    assert!(start_idx < end_idx, "source markers are out of order");
    &src[start_idx..end_idx]
}

fn span(src: &str, start: &str, end: &str) -> (usize, usize) {
    let start_idx = src.find(start).expect("start marker must exist");
    let end_idx = src.find(end).expect("end marker must exist");
    assert!(start_idx < end_idx, "source markers are out of order");
    (start_idx, end_idx)
}

#[wasm_bindgen_test(unsupported = test)]
fn canonical_step_section_does_not_mutate_commit_owned_state() {
    let src = include_str!("../src/vm.rs");
    let step_section = between(
        src,
        "// ---- Per-instruction step functions",
        "fn commit_pack(",
    );

    let forbidden_patterns = [
        "self.sessions.update_type(",
        "self.sessions.update_original(",
        "self.sessions.remove_type(",
        "self.obs_trace.push(",
        "self.obs_trace.extend(",
        "self.coroutines[coro_idx].pc =",
        "self.coroutines[coro_idx].pc +=",
        "self.coroutines[coro_idx].status =",
    ];

    let mut violations = Vec::new();
    for pattern in forbidden_patterns {
        if step_section.contains(pattern) {
            violations.push(pattern);
        }
    }

    assert!(
        violations.is_empty(),
        "step section mutates commit-owned state directly: {}",
        violations.join(", ")
    );
}

#[wasm_bindgen_test(unsupported = test)]
fn commit_pack_contains_commit_owned_mutation_sites() {
    let src = include_str!("../src/vm.rs");
    let commit_section = between(src, "fn commit_pack(", "\n}\n\n#[cfg(test)]");

    let required_patterns = [
        "self.sessions.update_type(",
        "self.sessions.update_original(",
        "self.sessions.remove_type(",
        "self.obs_trace.extend(",
        "coro.pc +=",
        "coro.status =",
    ];

    let missing: Vec<_> = required_patterns
        .iter()
        .copied()
        .filter(|pattern| !commit_section.contains(pattern))
        .collect();

    assert!(
        missing.is_empty(),
        "commit_pack is missing expected mutation sites: {}",
        missing.join(", ")
    );
}

#[wasm_bindgen_test(unsupported = test)]
fn commit_pack_is_only_owner_of_type_state_mutations() {
    let src = include_str!("../src/vm.rs");
    let (commit_start, commit_end) = span(src, "fn commit_pack(", "\n}\n\n#[cfg(test)]");
    let patterns = [
        "self.sessions.update_type(",
        "self.sessions.update_original(",
        "self.sessions.remove_type(",
    ];

    for pattern in patterns {
        let mut scan_from = 0usize;
        let mut seen = 0usize;
        while let Some(rel) = src[scan_from..].find(pattern) {
            let idx = scan_from + rel;
            seen += 1;
            assert!(
                idx >= commit_start && idx < commit_end,
                "type-state mutation `{pattern}` occurs outside commit_pack at byte index {idx}"
            );
            scan_from = idx + pattern.len();
        }
        assert!(seen > 0, "expected to see `{pattern}` inside commit_pack");
    }
}
