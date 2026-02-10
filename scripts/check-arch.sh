#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUST_DIR="${ROOT_DIR}/rust"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

errors=0
warnings=0

DETERMINISM_RUNTIME_SCOPE=(
  "${RUST_DIR}/vm/src"
  "${RUST_DIR}/simulator/src"
  "${RUST_DIR}/choreography/src/simulation"
)

DETERMINISM_TEST_SCOPE=(
  "${RUST_DIR}/vm/tests"
  "${RUST_DIR}/simulator/tests"
  "${RUST_DIR}/choreography/tests/simulation_tests.rs"
)

VM_KERNEL_SCOPE=(
  "${RUST_DIR}/vm/src/kernel.rs"
  "${RUST_DIR}/vm/src/vm.rs"
  "${RUST_DIR}/vm/src/threaded.rs"
  "${RUST_DIR}/vm/src/scheduler.rs"
  "${RUST_DIR}/vm/src/session.rs"
  "${RUST_DIR}/vm/src/coroutine.rs"
  "${RUST_DIR}/vm/src/exec/mod.rs"
  "${RUST_DIR}/vm/src/exec/comm.rs"
  "${RUST_DIR}/vm/src/exec/session.rs"
  "${RUST_DIR}/vm/src/exec/guard_effect.rs"
  "${RUST_DIR}/vm/src/exec/speculation.rs"
  "${RUST_DIR}/vm/src/exec/ownership.rs"
  "${RUST_DIR}/vm/src/exec/control.rs"
  "${RUST_DIR}/vm/src/exec/helpers.rs"
)

print_section() {
  echo ""
  echo -e "${BLUE}== $1 ==${NC}"
}

print_hits() {
  local severity="$1"
  local title="$2"
  local matches="$3"
  local recommendation="$4"
  local count=0
  if [[ -n "${matches}" ]]; then
    count="$(printf '%s\n' "${matches}" | sed '/^$/d' | wc -l | tr -d ' ')"
  fi

  if [[ "${count}" == "0" ]]; then
    echo -e "${GREEN}OK${NC}  ${title}"
    return
  fi

  if [[ "${severity}" == "error" ]]; then
    errors=$((errors + count))
    echo -e "${RED}VIOLATION${NC}  ${title} (${count})"
  else
    warnings=$((warnings + count))
    echo -e "${YELLOW}WARNING${NC}  ${title} (${count})"
  fi

  if [[ -n "${recommendation}" ]]; then
    echo "Recommended action: ${recommendation}"
  fi

  printf '%s\n' "${matches}" | sed -n '1,25p'
  if [[ "${count}" -gt 25 ]]; then
    echo "... (${count} total, truncated to 25)"
  fi
}

scan_scope_hits() {
  local pattern="$1"
  shift

  local path
  local out
  local hits=""
  for path in "$@"; do
    [[ -e "${path}" ]] || continue
    out="$(rg -n --pcre2 "${pattern}" "${path}" -g '*.rs' || true)"
    if [[ -n "${out}" ]]; then
      hits+="${out}"$'\n'
    fi
  done

  printf '%s\n' "${hits}" | sed '/^$/d' | sort -u || true
}

filter_out_paths() {
  local matches="$1"
  shift

  local filtered="${matches}"
  local path
  for path in "$@"; do
    filtered="$(printf '%s\n' "${filtered}" | rg -v "${path}" || true)"
  done
  printf '%s\n' "${filtered}" | sed '/^$/d' || true
}

filter_float_matches_to_code_tokens() {
  local matches="$1"

  printf '%s\n' "${matches}" | awk '
    {
      raw = $0
      body = $0
      sub(/^[^:]+:[0-9]+:/, "", body)

      # Drop pure line comments early.
      if (body ~ /^[[:space:]]*\/\//) {
        next
      }

      # Remove trailing line comment and string literals, then re-check token.
      sub(/\/\/.*/, "", body)
      while (match(body, /"([^"\\]|\\.)*"/)) {
        body = substr(body, 1, RSTART - 1) substr(body, RSTART + RLENGTH)
      }

      if (body ~ /(^|[^[:alnum:]_])(f32|f64)([^[:alnum:]_]|$)/) {
        print raw
      }
    }
  ' | sed '/^$/d' | sort -u || true
}

# Filter out matches that appear in comments (// or /// or //!)
filter_out_comments() {
  local matches="$1"

  printf '%s\n' "${matches}" | awk '
    {
      raw = $0
      body = $0
      sub(/^[^:]+:[0-9]+:/, "", body)

      # Drop lines that are pure comments
      if (body ~ /^[[:space:]]*\/\//) {
        next
      }

      print raw
    }
  ' | sed '/^$/d' || true
}

scan_serde_derived_usize_hits() {
  local file="$1"
  awk -v file="$file" '
    function count_braces(s,   tmp, opens, closes) {
      tmp = s
      opens = gsub(/\{/, "{", tmp)
      tmp = s
      closes = gsub(/\}/, "}", tmp)
      return opens - closes
    }

    BEGIN {
      in_derive = 0
      derive_has_serde = 0
      pending_serde_type = 0
      in_type = 0
      brace_depth = 0
    }

    {
      line = $0

      # Handle one-line attribute + type forms:
      # #[derive(Serialize, ...)] pub struct Foo { ... }
      if (!in_type && line ~ /#[[:space:]]*\[[[:space:]]*derive[[:space:]]*\([^]]*(Serialize|Deserialize)[^]]*\)[[:space:]]*][[:space:]]*(pub[[:space:]]+)?(struct|enum)[[:space:]]+[A-Za-z_][A-Za-z0-9_]*/) {
        if (line ~ /\busize\b/) {
          print file ":" NR ":" line
        }
        brace_depth = count_braces(line)
        if (brace_depth > 0) {
          in_type = 1
          pending_serde_type = 1
        } else {
          in_type = 0
          pending_serde_type = 0
        }
        next
      }

      if (!in_type) {
        if (in_derive) {
          if (line ~ /(Serialize|Deserialize)/) {
            derive_has_serde = 1
          }
          if (line ~ /]/) {
            if (derive_has_serde) {
              pending_serde_type = 1
            }
            in_derive = 0
            derive_has_serde = 0
          }
          next
        }

        if (line ~ /^[[:space:]]*#[[:space:]]*\[[[:space:]]*derive[[:space:]]*\(/) {
          in_derive = 1
          if (line ~ /(Serialize|Deserialize)/) {
            derive_has_serde = 1
          }
          if (line ~ /]/) {
            if (derive_has_serde) {
              pending_serde_type = 1
            }
            in_derive = 0
            derive_has_serde = 0
          }
          next
        }

        if (pending_serde_type && line ~ /^[[:space:]]*(pub[[:space:]]+)?(struct|enum)[[:space:]]+[A-Za-z_][A-Za-z0-9_]*/) {
          if (line ~ /\busize\b/) {
            print file ":" NR ":" line
          }
          brace_depth = count_braces(line)
          if (brace_depth > 0) {
            in_type = 1
          } else {
            pending_serde_type = 0
          }
          next
        }

        # Reset pending derive marker once we hit a non-attribute item that is
        # clearly not the associated type declaration.
        if (pending_serde_type) {
          if (line ~ /^[[:space:]]*$/ || line ~ /^[[:space:]]*\/\// || line ~ /^[[:space:]]*#[[:space:]]*\[/) {
            next
          }
          pending_serde_type = 0
        }

        next
      }

      if (line ~ /\busize\b/) {
        print file ":" NR ":" line
      }
      brace_depth += count_braces(line)
      if (brace_depth <= 0) {
        in_type = 0
        pending_serde_type = 0
      }
    }
  ' "$file"
}

print_section "Rust Architectural Style Checks"
echo "Scanning: ${RUST_DIR}"

# 1) Unsafe in production source.
unsafe_hits="$(rg -n --pcre2 '\bunsafe\s*(fn|\{)' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
print_hits "error" "unsafe usage in non-test Rust source" "${unsafe_hits}" "Remove unsafe usage, or isolate it behind a tiny module boundary with explicit invariants and targeted tests."

# 2) Public APIs with bool parameters.
bool_param_hits="$(rg -n --pcre2 'pub\s+fn\s+\w+\s*\([^)]*:\s*bool\b' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
print_hits "warning" "public API bool parameters (prefer enums/options)" "${bool_param_hits}" "Replace bool parameters with a small enum or options struct so call sites are self-describing."

# 3) let _ = ... ignored results (only flag if no explanatory comment on same or preceding line).
ignored_result_raw="$(rg -n --pcre2 -B1 'let\s+_\s*=\s*' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
# Filter out instances with an explanatory comment
ignored_result_hits="$(printf '%s\n' "${ignored_result_raw}" | awk '
  # Comment on preceding line explaining the ignore
  /\/\/.*[Ii]gnore|\/\/.*unused|\/\/.*intentional|\/\/.*discard/ {
    skip_next = 1
    next
  }
  # The actual let _ = line
  /let\s+_\s*=/ {
    if (!skip_next) {
      print
    }
    skip_next = 0
    next
  }
  { skip_next = 0 }
' || true)"
print_hits "warning" "ignored results via let _ =" "${ignored_result_hits}" "Handle the Result explicitly (match/if let), or document intentional discard with an inline reason comment."

# 4) Potentially unbounded loops (only flag if not preceded by a bound/loop comment).
loop_hits_raw="$(rg -n --pcre2 -B1 '^\s*loop\s*\{' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
# Filter out loops that have BOUND/Forever/Termination comments on the preceding line
loop_hits="$(printf '%s\n' "${loop_hits_raw}" | awk '
  /BOUND:|Forever|Termination:|exits on|until .* signal|until .* closed|terminates when/ {
    skip_next = 1
    next
  }
  /^\s*loop\s*\{/ {
    if (!skip_next) {
      print
    }
    skip_next = 0
    next
  }
  { skip_next = 0 }
' || true)"
print_hits "warning" "potentially unbounded loop blocks (document invariant/bound)" "${loop_hits}" "Add an explicit bound or a nearby invariant comment explaining termination/forever-loop intent."

# 5) TODO/FIXME/HACK markers in source.
todo_hits="$(rg -n --pcre2 '\b(TODO|FIXME|HACK|XXX)\b' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
print_hits "warning" "technical-debt markers in source" "${todo_hits}" "Resolve the marker or convert it into a tracked issue reference with a concrete follow-up plan."

# 6) Large magic-number comparisons.
magic_hits="$(rg -n --pcre2 '(<=|>=|<|>)\s*[0-9]{3,}\b' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
print_hits "warning" "large magic-number comparisons (prefer named constants)" "${magic_hits}" "Extract the numeric threshold into a named constant with units (for example, *_MS, *_BYTES, *_MAX)."

# 7) usize in serde-derived struct/enum definitions.
serde_files="$(rg -l --pcre2 '(Serialize|Deserialize)' "${RUST_DIR}" -g '*.rs' | rg '/src/' || true)"
serde_usize_hits=""
if [[ -n "${serde_files}" ]]; then
  while IFS= read -r file; do
    [[ -z "${file}" ]] && continue
    lines="$(scan_serde_derived_usize_hits "${file}")"
    [[ -z "${lines}" ]] && continue
    serde_usize_hits+="${lines}"$'\n'
  done <<< "${serde_files}"
fi
print_hits "warning" "usize in serde-derived struct/enum definitions" "${serde_usize_hits}" "For serialized/persisted schema fields, replace usize with explicit-width integers (u32/u64), and reserve usize for in-memory indexing only."

print_section "Numeric Safety Checks"

# 8) Fixed-point policy: use only telltale_types::FixedQ32 wrapper API.
raw_fixed_hits="$(rg -n --pcre2 '\bfixed::' "${RUST_DIR}" -g '*.rs' | rg -v '/types/src/fixed_q32.rs:' || true)"
print_hits "error" "raw fixed crate usage outside FixedQ32 wrapper" "${raw_fixed_hits}" "Use telltale_types::FixedQ32 (and its checked constructors/ops). Do not import fixed:: types directly outside rust/types/src/fixed_q32.rs."

# 9) Strict config schema policy: no float-typed config fields.
config_float_field_hits="$(rg -n --pcre2 'pub\s+[A-Za-z_][A-Za-z0-9_]*\s*:\s*(Option<\s*)?f(32|64)\b' "${RUST_DIR}" -g '*config*.rs' -g '*invariants*.rs' || true)"
print_hits "error" "float-typed fields in config/schema definitions" "${config_float_field_hits}" "Replace float config/schema fields with FixedQ32 or explicit integer-scaled types so serialized config remains deterministic."

# 10) Strict fixed-point config decoding: FixedQ32 must not accept float tokens.
fixed_q32_float_decode_hits="$(rg -n --pcre2 'visit_f(32|64)\s*\(' "${RUST_DIR}/types/src/fixed_q32.rs" || true)"
print_hits "error" "FixedQ32 float-token deserialization path" "${fixed_q32_float_decode_hits}" "Reject JSON float tokens for FixedQ32 deserialization; accept deterministic encodings only (decimal strings or explicit fixed-point integer forms)."

print_section "Determinism and Effects Checks"
echo "Determinism runtime scope:"
for path in "${DETERMINISM_RUNTIME_SCOPE[@]}"; do
  if [[ -e "${path}" ]]; then
    echo "  - ${path}"
  fi
done
echo "Determinism test/simulation scope:"
for path in "${DETERMINISM_TEST_SCOPE[@]}"; do
  if [[ -e "${path}" ]]; then
    echo "  - ${path}"
  fi
done

# 11) Floating-point types in deterministic runtime/simulation scope.
float_type_hits="$(scan_scope_hits '\b(f32|f64)\b' "${DETERMINISM_RUNTIME_SCOPE[@]}" "${DETERMINISM_TEST_SCOPE[@]}")"
float_type_hits="$(filter_float_matches_to_code_tokens "${float_type_hits}")"
float_type_hits="$(filter_out_paths "${float_type_hits}" '/vm/tests/helpers/')"
print_hits "error" "floating-point types in deterministic VM/simulation scope" "${float_type_hits}" "Replace floating-point values with deterministic fixed-point or integer representations (for example, scaled i64/u64 newtypes)."

# 12) Direct host nondeterminism must not appear in deterministic scope.
# Note: MockClock's Instant::now() is documented as unavoidable - Rust's Instant
# cannot be constructed synthetically. Only the offset matters for determinism.
nondet_hits="$(scan_scope_hits 'SystemTime::now\(|Instant::now\(|UNIX_EPOCH|rand::thread_rng\(|thread_rng\(|rand::random\(|getrandom\(|from_entropy\(|OsRng\b|Utc::now\(|Local::now\(' "${DETERMINISM_RUNTIME_SCOPE[@]}" "${DETERMINISM_TEST_SCOPE[@]}")"
nondet_hits="$(filter_out_paths "${nondet_hits}" 'kernel_nondeterminism_guard.rs:')"
nondet_hits="$(filter_out_paths "${nondet_hits}" 'simulation/clock.rs:.*start: Instant::now')"
nondet_hits="$(filter_out_comments "${nondet_hits}")"
print_hits "error" "direct host nondeterminism in deterministic VM/simulation scope" "${nondet_hits}" "Route entropy and wall-clock access through explicit effect injection APIs; keep core runtime logic pure and replayable."

# 13) VM kernel must not touch host I/O/process/env APIs directly.
kernel_side_effect_hits="$(scan_scope_hits 'std::fs::|std::net::|std::env::var\(|std::process::Command|tokio::fs::|tokio::net::|tokio::process::Command' "${VM_KERNEL_SCOPE[@]}")"
print_hits "error" "direct host side effects in VM kernel sources" "${kernel_side_effect_hits}" "Move host I/O, process, network, and environment reads behind the VM effect layer and inject handles at the boundary."

# 14) HashMap/HashSet in deterministic scope can destabilize iteration order.
hash_collection_hits="$(scan_scope_hits '\b(HashMap|HashSet)\b' "${DETERMINISM_RUNTIME_SCOPE[@]}")"
print_hits "warning" "hash-based collections in deterministic VM/simulation scope" "${hash_collection_hits}" "Prefer BTreeMap/BTreeSet for stable ordering, or enforce deterministic ordering before iterating/emitting externally visible results."

# 15) Thread scheduling/time sleeps in deterministic scope.
thread_nondet_hits="$(scan_scope_hits 'std::thread::spawn\(|std::thread::sleep\(|tokio::spawn\(|tokio::time::sleep\(' "${DETERMINISM_RUNTIME_SCOPE[@]}" "${DETERMINISM_TEST_SCOPE[@]}")"
print_hits "error" "direct thread scheduling/timer calls in deterministic VM/simulation scope" "${thread_nondet_hits}" "Model scheduling and timers as explicit scheduler/effect inputs so replay behavior is controlled and cross-target equivalent."

echo ""
echo -e "Errors:   ${RED}${errors}${NC}"
echo -e "Warnings: ${YELLOW}${warnings}${NC}"

if [[ "${errors}" -gt 0 ]]; then
  exit 1
fi

exit 0
