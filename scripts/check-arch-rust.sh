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
summary_lines=""

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

CORE_RUNTIME_SCOPE=(
  "${RUST_DIR}/vm/src"
  "${RUST_DIR}/simulator/src"
  "${RUST_DIR}/choreography/src"
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
    summary_lines+=$'OK\t'"${title}"$'\t0\n'
    return
  fi

  if [[ "${severity}" == "error" ]]; then
    errors=$((errors + count))
    echo -e "${RED}VIOLATION${NC}  ${title} (${count})"
    summary_lines+=$'ERROR\t'"${title}"$'\t'"${count}"$'\n'
  else
    warnings=$((warnings + count))
    echo -e "${YELLOW}WARNING${NC}  ${title} (${count})"
    summary_lines+=$'WARN\t'"${title}"$'\t'"${count}"$'\n'
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

scan_recursive_function_calls() {
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
      in_fn = 0
      fn_name = ""
      fn_start = 0
      fn_body = ""
      brace_depth = 0
      suppress_fn = 0
      prev_line = ""
    }

    {
      line = $0

      if (!in_fn) {
        if (line ~ /^[[:space:]]*(pub(\([^)]*\))?[[:space:]]*)?(async[[:space:]]+)?(const[[:space:]]+)?(unsafe[[:space:]]+)?fn[[:space:]]+[A-Za-z_][A-Za-z0-9_]*/) {
          fn_name = line
          sub(/.*fn[[:space:]]+/, "", fn_name)
          sub(/[^A-Za-z0-9_].*/, "", fn_name)
          fn_start = NR
          fn_body = ""
          brace_depth = count_braces(line)
          in_fn = 1
          suppress_fn = (prev_line ~ /(RECURSION_SAFE|RECURSION_OK|bounded recursion)/)

          # Trait signatures and extern declarations end with a semicolon and have no body.
          if (brace_depth <= 0 && line ~ /;[[:space:]]*$/) {
            in_fn = 0
            fn_name = ""
            suppress_fn = 0
          }

          prev_line = line
          next
        }

        prev_line = line
        next
      }

      fn_body = fn_body "\n" line
      brace_depth += count_braces(line)
      if (brace_depth <= 0) {
        if (!suppress_fn) {
          pattern = "(^|[^A-Za-z0-9_:.])" fn_name "[[:space:]]*\\("
          if (fn_body ~ pattern) {
            printf "%s:%d: fn %s appears recursive (add bound/invariant comment if intentional)\n", file, fn_start, fn_name
          }
        }
        in_fn = 0
        fn_name = ""
        suppress_fn = 0
      }

      prev_line = line
    }
  ' "$file"
}

scan_lock_await_hits() {
  local file="$1"
  awk -v file="$file" '
    BEGIN {
      track = 0
      start_line = 0
      guard_name = ""
      window = 0
      prev_line = ""
    }

    {
      line = $0

      # Track statements like:
      # let guard = lock.read().await;
      # let mut guard = state.lock().await?;
      if (line ~ /let[[:space:]]+(mut[[:space:]]+)?[A-Za-z_][A-Za-z0-9_]*[[:space:]]*=[^;]*(lock|read|write)\([^)]*\)[[:space:]]*\.await/) {
        if (line ~ /LOCK_AWAIT_OK/ || prev_line ~ /LOCK_AWAIT_OK/) {
          prev_line = line
          next
        }
        tmp = line
        sub(/.*let[[:space:]]+/, "", tmp)
        sub(/=.*/, "", tmp)
        gsub(/[[:space:]]+/, "", tmp)
        gsub(/^mut/, "", tmp)
        guard_name = tmp
        start_line = NR
        window = 12
        track = 1
        prev_line = line
        next
      }

      if (!track) {
        prev_line = line
        next
      }

      if (window <= 0) {
        track = 0
        guard_name = ""
        prev_line = line
        next
      }

      # Ignore comments and blank lines in the lookahead window.
      if (line ~ /^[[:space:]]*$/ || line ~ /^[[:space:]]*\/\//) {
        window -= 1
        prev_line = line
        next
      }

      # Explicit drop/rebind ends the hold window.
      if (line ~ ("drop[[:space:]]*\\([[:space:]]*" guard_name "[[:space:]]*\\)") ||
          line ~ ("let[[:space:]]+(mut[[:space:]]+)?" guard_name "[[:space:]]*=")) {
        track = 0
        guard_name = ""
        prev_line = line
        next
      }

      if (line ~ /\.await/) {
        printf "%s:%d: lock/read/write guard `%s` may be held across await within %d-line window\n", file, start_line, guard_name, 12
        track = 0
        guard_name = ""
        prev_line = line
        next
      }

      window -= 1
      prev_line = line
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
# Also exclude inline #[test] functions and #[cfg(test)] modules.
ignored_result_raw="$(rg -n --pcre2 -B1 'let\s+_\s*=\s*' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
# Filter out instances with an explanatory comment (preceding line or same line).
# Recognized patterns: ignore, unused, intentional, discard, infallible, ok to fail,
# always succeeds, cannot fail, best-effort, fire-and-forget, side effect only.
# Also filter out lines that appear to be in test context (preceded by #[test]).
ignored_result_hits="$(printf '%s\n' "${ignored_result_raw}" | awk '
  # Skip #[test] or #[cfg(test)] markers and the next let _ =
  /#\[(test|cfg\(test\))\]/ {
    skip_next = 1
    next
  }
  # Comment on preceding line explaining the ignore
  /\/\/.*([Ii]gnor|[Uu]nused|[Ii]ntentional|[Dd]iscard|[Ii]nfallible|ok to fail|always succeed|cannot fail|best.effort|fire.and.forget|side.effect|not needed|value discarded)/ {
    skip_next = 1
    next
  }
  # The actual let _ = line - check for same-line comment too
  /let\s+_\s*=/ {
    if (!skip_next) {
      # Check if the line itself has an explanatory trailing comment
      if ($0 ~ /\/\/.*([Ii]gnor|[Uu]nused|[Ii]ntentional|[Dd]iscard|[Ii]nfallible|ok to fail|always succeed|cannot fail|best.effort|fire.and.forget|side.effect|not needed|value discarded)/) {
        skip_next = 0
        next
      }
      print
    }
    skip_next = 0
    next
  }
  { skip_next = 0 }
' || true)"

# Post-filter: exclude matches inside #[cfg(test)] modules by checking file context.
filter_out_test_modules() {
  while IFS= read -r line; do
    [[ -z "${line}" ]] && continue
    file="$(echo "${line}" | cut -d: -f1)"
    lineno="$(echo "${line}" | cut -d: -f2)"
    # Find the line number where #[cfg(test)] mod tests starts
    test_mod_start="$(rg -n '#\[cfg\(test\)\]' "${file}" 2>/dev/null | head -1 | cut -d: -f1 || true)"
    if [[ -n "${test_mod_start}" ]] && [[ "${lineno}" -gt "${test_mod_start}" ]]; then
      # This line is inside the test module, skip it
      continue
    fi
    echo "${line}"
  done
}
ignored_result_hits="$(printf '%s\n' "${ignored_result_hits}" | filter_out_test_modules || true)"

print_hits "warning" "ignored results via let _ =" "${ignored_result_hits}" "Handle the Result explicitly, or add a comment with: ignore, discard, infallible, side-effect, best-effort, etc."

# 4) Potentially unbounded loops (only flag if not preceded by a bound/loop comment).
loop_hits_raw="$(rg -n --pcre2 -B1 '^\s*loop\s*\{' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
# Filter out loops that have BOUND/Forever/Termination comments on the preceding line
loop_hits="$(printf '%s\n' "${loop_hits_raw}" | awk '
  /BOUND:|Forever|Termination:|exits on|until .* signal|until .* closed|terminates when/ {
    skip_next = 1
    next
  }
  /^[[:space:]]*loop[[:space:]]*\{/ {
    if (!skip_next) {
      print
    }
    skip_next = 0
    next
  }
  { skip_next = 0 }
' || true)"
print_hits "warning" "potentially unbounded loop blocks (document invariant/bound)" "${loop_hits}" "Add an explicit bound or a nearby invariant comment explaining termination/forever-loop intent."

# 4b) while true loops should be documented like loop{}.
while_true_hits_raw="$(rg -n --pcre2 -B1 '^\s*while\s+true\s*\{' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
while_true_hits="$(printf '%s\n' "${while_true_hits_raw}" | awk '
  /BOUND:|Forever|Termination:|exits on|until .* signal|until .* closed|terminates when/ {
    skip_next = 1
    next
  }
  /^[[:space:]]*while[[:space:]]+true[[:space:]]*\{/ {
    if (!skip_next) {
      print
    }
    skip_next = 0
    next
  }
  { skip_next = 0 }
' || true)"
print_hits "warning" "while true loops without bound/invariant notes" "${while_true_hits}" "Prefer bounded loops. If intentional, add a preceding invariant comment describing termination/forever-loop intent."

# 5) Avoid compound assertions in one assert call.
compound_assert_hits="$(rg -n --pcre2 '\b(debug_)?assert!\s*\([^)]*(&&|\|\|)[^)]*\)' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
print_hits "warning" "compound assertions in a single assert! call" "${compound_assert_hits}" "Split asserts into one invariant per assert! call so failures are precise and easier to diagnose."

# 6) TODO/FIXME/HACK markers in source.
todo_hits="$(rg -n --pcre2 '\b(TODO|FIXME|HACK|XXX)\b' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
print_hits "warning" "technical-debt markers in source" "${todo_hits}" "Resolve the marker or convert it into a tracked issue reference with a concrete follow-up plan."

# 7) Large magic-number comparisons.
magic_hits="$(rg -n --pcre2 '(<=|>=|<|>)\s*[0-9]{3,}\b' "${RUST_DIR}" -g '*.rs' | rg -v '/tests?/|/benches?/' || true)"
print_hits "warning" "large magic-number comparisons (prefer named constants)" "${magic_hits}" "Extract the numeric threshold into a named constant with units (for example, *_MS, *_BYTES, *_MAX)."

# 8) usize in serde-derived struct/enum definitions.
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

# 9) Recursive functions in core runtime scope should be explicitly justified.
recursive_hits=""
while IFS= read -r file; do
  [[ -z "${file}" ]] && continue
  blocks="$(scan_recursive_function_calls "${file}")"
  [[ -z "${blocks}" ]] && continue
  recursive_hits+="${blocks}"$'\n'
done < <(find "${CORE_RUNTIME_SCOPE[@]}" -name '*.rs' -type f 2>/dev/null | grep -v '/tests/' | grep -v '/benches/')
print_hits "warning" "potential recursion in core runtime modules" "${recursive_hits}" "Prefer iterative control flow. If recursion is intentional and bounded, add a nearby comment such as RECURSION_SAFE with the bound/invariant."

# 10) Limit-style constants should encode units in names.
limit_constant_hits="$(awk '
  function has_unit_token(name,    n,toks,i) {
    n = split(name, toks, "_")
    for (i = 1; i <= n; i++) {
      if (toks[i] ~ /^(MS|US|NS|SEC|SECS|SECOND|SECONDS|MINUTE|MINUTES|MINS|HOUR|HOURS|BYTES|BYTE|BITS|BIT|KB|MB|GB|COUNT|COUNTS|ENTRY|ENTRIES|ITEM|ITEMS|ATTEMPT|ATTEMPTS|INDEX|PRICE|UNIT|UNITS|PCT|PERCENT|RATIO|TICK|TICKS)$/) {
        return 1
      }
    }
    return 0
  }

  {
    line = $0
    if (line ~ /^[[:space:]]*(pub[[:space:]]+)?const[[:space:]]+[A-Z][A-Z0-9_]*[[:space:]]*:[[:space:]]*[ui][0-9]+/) {
      name = line
      sub(/^[[:space:]]*(pub[[:space:]]+)?const[[:space:]]+/, "", name)
      sub(/[[:space:]]*:.*$/, "", name)
      if (name == "MIN" || name == "MAX") {
        next
      }
      if (name ~ /(MAX|MIN|LIMIT|TIMEOUT|INTERVAL|BACKOFF|CAPACITY|SIZE|LENGTH|LEN|BATCH)/) {
        if (!has_unit_token(name)) {
          print FILENAME ":" FNR ":" line
        }
      }
    }
  }
' $(find "${RUST_DIR}" -name '*.rs' -type f | grep -v '/tests/' | grep -v '/benches/' ) || true)"
print_hits "warning" "limit-style constants without explicit unit tokens" "${limit_constant_hits}" "Rename constants to include units (for example, *_MS, *_BYTES, *_COUNT, *_TICKS) so bounds are unambiguous."

print_section "File and Block Size Checks"

count_non_test_lines() {
  local file="$1"
  awk '
    function strip_literals_and_comments(s,   out) {
      out = s
      sub(/\/\/.*/, "", out)
      while (match(out, /"([^"\\]|\\.)*"/)) {
        out = substr(out, 1, RSTART - 1) substr(out, RSTART + RLENGTH)
      }
      while (match(out, /'\''([^'\''\\]|\\.)*'\''/)) {
        out = substr(out, 1, RSTART - 1) substr(out, RSTART + RLENGTH)
      }
      return out
    }

    function count_braces(s,   tmp, opens, closes) {
      tmp = strip_literals_and_comments(s)
      opens = gsub(/\{/, "{", tmp)
      tmp = strip_literals_and_comments(s)
      closes = gsub(/\}/, "}", tmp)
      return opens - closes
    }

    BEGIN {
      in_cfg_test_attr = 0
      skip_test_mod_depth = 0
      count = 0
    }

    skip_test_mod_depth > 0 {
      skip_test_mod_depth += count_braces($0)
      if (skip_test_mod_depth <= 0) {
        skip_test_mod_depth = 0
      }
      next
    }

    /^[[:space:]]*#[[:space:]]*\[[[:space:]]*cfg[[:space:]]*\([[:space:]]*test[[:space:]]*\)[[:space:]]*]/ {
      in_cfg_test_attr = 1
      next
    }

    in_cfg_test_attr && /^[[:space:]]*mod[[:space:]]+[A-Za-z_][A-Za-z0-9_]*[[:space:]]*\{/ {
      skip_test_mod_depth = count_braces($0)
      if (skip_test_mod_depth <= 0) {
        skip_test_mod_depth = 0
      }
      in_cfg_test_attr = 0
      next
    }

    in_cfg_test_attr {
      if ($0 !~ /^[[:space:]]*$/ && $0 !~ /^[[:space:]]*#/) {
        in_cfg_test_attr = 0
      } else {
        next
      }
    }

    { count += 1 }

    END { print count }
  ' "$file"
}

# Files over 600 lines (should be split into modules).
large_file_hits=""
while IFS= read -r file; do
  [[ -z "${file}" ]] && continue
  lines="$(count_non_test_lines "${file}" | tr -d ' ')"
  if [[ "${lines}" -gt 600 ]]; then
    large_file_hits+="${file}:${lines} lines"$'\n'
  fi
done < <(find "${RUST_DIR}" -name '*.rs' -type f | grep -v '/target/' | grep -v '/tests/' | grep -v '/benches/' | grep -v '/examples/' | grep -v '/src/bin/')
print_hits "warning" "files over 600 lines (split into modules)" "${large_file_hits}" "Extract cohesive subsystems into separate modules (e.g., foo.rs -> foo/mod.rs + foo/bar.rs). Group by abstraction boundary, not arbitrary line count."

# Functions/blocks over 60 lines (should be refactored).
scan_large_blocks() {
  local file="$1"
  awk -v file="$file" '
    function strip_literals_and_comments(s,   out) {
      out = s
      sub(/\/\/.*/, "", out)
      while (match(out, /"([^"\\]|\\.)*"/)) {
        out = substr(out, 1, RSTART - 1) substr(out, RSTART + RLENGTH)
      }
      while (match(out, /'\''([^'\''\\]|\\.)*'\''/)) {
        out = substr(out, 1, RSTART - 1) substr(out, RSTART + RLENGTH)
      }
      return out
    }

    function count_braces(s,   tmp, opens, closes) {
      tmp = strip_literals_and_comments(s)
      opens = gsub(/\{/, "{", tmp)
      tmp = strip_literals_and_comments(s)
      closes = gsub(/\}/, "}", tmp)
      return opens - closes
    }

    BEGIN {
      in_fn = 0
      fn_start = 0
      fn_name = ""
      ignore_fn = 0
      brace_depth = 0
      in_cfg_test_attr = 0
      skip_test_mod_depth = 0
      pending_test_attr = 0
      pending_large_fn_allow = 0
    }

    skip_test_mod_depth > 0 {
      skip_test_mod_depth += count_braces($0)
      if (skip_test_mod_depth <= 0) {
        skip_test_mod_depth = 0
      }
      next
    }

    !in_fn && /^[[:space:]]*#[[:space:]]*\[[[:space:]]*cfg[[:space:]]*\([[:space:]]*test[[:space:]]*\)[[:space:]]*]/ {
      in_cfg_test_attr = 1
      next
    }

    !in_fn && /^[[:space:]]*#[[:space:]]*\[[[:space:]]*test[[:space:]]*]/ {
      pending_test_attr = 1
      next
    }

    !in_fn && /^[[:space:]]*#[[:space:]]*\[[[:space:]]*allow[[:space:]]*\([[:space:]]*clippy::too_many_lines[[:space:]]*\)[[:space:]]*]/ {
      pending_large_fn_allow = 1
      next
    }

    !in_fn && in_cfg_test_attr && /^[[:space:]]*mod[[:space:]]+[A-Za-z_][A-Za-z0-9_]*[[:space:]]*\{/ {
      skip_test_mod_depth = count_braces($0)
      if (skip_test_mod_depth <= 0) {
        skip_test_mod_depth = 0
      }
      in_cfg_test_attr = 0
      pending_test_attr = 0
      pending_large_fn_allow = 0
      next
    }

    !in_fn && in_cfg_test_attr {
      if ($0 !~ /^[[:space:]]*$/ && $0 !~ /^[[:space:]]*#/) {
        in_cfg_test_attr = 0
      } else {
        next
      }
    }

    # Match function definitions (pub/pub(crate)/async/const/unsafe fn name)
    !in_fn && /^[[:space:]]*(pub(\([^)]*\))?[[:space:]]*)?(async[[:space:]]+)?(const[[:space:]]+)?(unsafe[[:space:]]+)?fn[[:space:]]+[A-Za-z_][A-Za-z0-9_]*/ {
      in_fn = 1
      fn_start = NR
      # Extract function name
      fn_name = $0
      sub(/.*fn[[:space:]]+/, "", fn_name)
      sub(/[^A-Za-z0-9_].*/, "", fn_name)
      ignore_fn = (pending_test_attr || pending_large_fn_allow || fn_name ~ /^test_/)
      pending_test_attr = 0
      pending_large_fn_allow = 0
      brace_depth = count_braces($0)
      if (brace_depth == 0 && $0 ~ /\{[[:space:]]*$/) {
        brace_depth = 1
      }
      next
    }

    !in_fn && pending_large_fn_allow {
      if ($0 !~ /^[[:space:]]*$/ && $0 !~ /^[[:space:]]*#/ && $0 !~ /^[[:space:]]*\/\//) {
        pending_large_fn_allow = 0
      } else {
        next
      }
    }

    in_fn {
      brace_depth += count_braces($0)
      if (brace_depth <= 0) {
        fn_len = NR - fn_start + 1
        if (!ignore_fn && fn_len > 60) {
          printf "%s:%d: fn %s (%d lines)\n", file, fn_start, fn_name, fn_len
        }
        in_fn = 0
        fn_name = ""
        ignore_fn = 0
      }
    }
  ' "$file"
}

large_block_hits=""
while IFS= read -r file; do
  [[ -z "${file}" ]] && continue
  blocks="$(scan_large_blocks "${file}")"
  [[ -z "${blocks}" ]] && continue
  large_block_hits+="${blocks}"$'\n'
done < <(find "${RUST_DIR}" -name '*.rs' -type f | grep -v '/target/' | grep -v '/tests/' | grep -v '/benches/' | grep -v '/examples/' | grep -v '/src/bin/')
print_hits "warning" "functions over 60 lines (refactor into smaller units)" "${large_block_hits}" "Extract logical steps into helper functions. Each function should do one thing. Compose small functions to build complex behavior."

# VM core lint-allow policy: keep suppressions narrow and explicit.
vm_core_allow_hits="$(rg -n --pcre2 '^[[:space:]]*#[[:space:]]*\\[[[:space:]]*allow\\([[:space:]]*clippy::[^)]+\\)[[:space:]]*\\]' "${RUST_DIR}/vm/src" -g '*.rs' || true)"
vm_core_allow_hits="$(printf '%s\n' "${vm_core_allow_hits}" | rg -v 'clippy::(as_conversions|derivable_impls|field_reassign_with_default)' || true)"
print_hits "warning" "broad clippy allow annotations in vm core paths" "${vm_core_allow_hits}" "Remove broad vm-core lint suppressions or replace them with smaller helper refactors. Keep only narrowly justified allows with an adjacent rationale comment."

print_section "Numeric Safety Checks"

# 11) Fixed-point policy: use only telltale_types::FixedQ32 wrapper API.
raw_fixed_hits="$(rg -n --pcre2 '\bfixed::' "${RUST_DIR}" -g '*.rs' | rg -v '/types/src/fixed_q32.rs:' || true)"
print_hits "error" "raw fixed crate usage outside FixedQ32 wrapper" "${raw_fixed_hits}" "Use telltale_types::FixedQ32 (and its checked constructors/ops). Do not import fixed:: types directly outside rust/types/src/fixed_q32.rs."

# 12) Strict config schema policy: no float-typed config fields.
config_float_field_hits="$(rg -n --pcre2 'pub\s+[A-Za-z_][A-Za-z0-9_]*\s*:\s*(Option<\s*)?f(32|64)\b' "${RUST_DIR}" -g '*config*.rs' -g '*invariants*.rs' || true)"
print_hits "error" "float-typed fields in config/schema definitions" "${config_float_field_hits}" "Replace float config/schema fields with FixedQ32 or explicit integer-scaled types so serialized config remains deterministic."

# 13) Strict fixed-point config decoding: FixedQ32 must not accept float tokens.
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

# 14) Floating-point types in deterministic runtime/simulation scope.
float_type_hits="$(scan_scope_hits '\b(f32|f64)\b' "${DETERMINISM_RUNTIME_SCOPE[@]}" "${DETERMINISM_TEST_SCOPE[@]}")"
float_type_hits="$(filter_float_matches_to_code_tokens "${float_type_hits}")"
float_type_hits="$(filter_out_paths "${float_type_hits}" '/vm/tests/helpers/')"
print_hits "error" "floating-point types in deterministic VM/simulation scope" "${float_type_hits}" "Replace floating-point values with deterministic fixed-point or integer representations (for example, scaled i64/u64 newtypes)."

# 15) Direct host nondeterminism must not appear in deterministic scope.
# Note: MockClock's Instant::now() is documented as unavoidable - Rust's Instant
# cannot be constructed synthetically. Only the offset matters for determinism.
nondet_hits="$(scan_scope_hits 'SystemTime::now\(|Instant::now\(|UNIX_EPOCH|rand::thread_rng\(|thread_rng\(|rand::random\(|getrandom\(|from_entropy\(|OsRng\b|Utc::now\(|Local::now\(' "${DETERMINISM_RUNTIME_SCOPE[@]}" "${DETERMINISM_TEST_SCOPE[@]}")"
nondet_hits="$(filter_out_paths "${nondet_hits}" 'kernel_nondeterminism_guard.rs:')"
nondet_hits="$(filter_out_paths "${nondet_hits}" 'simulation/clock.rs:.*start: Instant::now')"
nondet_hits="$(filter_out_comments "${nondet_hits}")"
print_hits "error" "direct host nondeterminism in deterministic VM/simulation scope" "${nondet_hits}" "Route entropy and wall-clock access through explicit effect injection APIs; keep core runtime logic pure and replayable."

# 16) Potential lock-held-across-await patterns.
lock_await_hits=""
while IFS= read -r file; do
  [[ -z "${file}" ]] && continue
  lines="$(scan_lock_await_hits "${file}")"
  [[ -z "${lines}" ]] && continue
  lock_await_hits+="${lines}"$'\n'
done < <(find "${RUST_DIR}" -name '*.rs' -type f | grep -v '/tests/' | grep -v '/benches/')
print_hits "warning" "potential lock-held-across-await patterns" "${lock_await_hits}" "Avoid holding lock guards across .await boundaries. Narrow lock scope or clone needed data before awaiting."

# 17) VM kernel must not touch host I/O/process/env APIs directly.
kernel_side_effect_hits="$(scan_scope_hits 'std::fs::|std::net::|std::env::var\(|std::process::Command|tokio::fs::|tokio::net::|tokio::process::Command' "${VM_KERNEL_SCOPE[@]}")"
print_hits "error" "direct host side effects in VM kernel sources" "${kernel_side_effect_hits}" "Move host I/O, process, network, and environment reads behind the VM effect layer and inject handles at the boundary."

# 18) HashMap/HashSet in deterministic scope can destabilize iteration order.
hash_collection_hits="$(scan_scope_hits '\b(HashMap|HashSet)\b' "${DETERMINISM_RUNTIME_SCOPE[@]}")"
print_hits "warning" "hash-based collections in deterministic VM/simulation scope" "${hash_collection_hits}" "Prefer BTreeMap/BTreeSet for stable ordering, or enforce deterministic ordering before iterating/emitting externally visible results."

# 19) Thread scheduling/time sleeps in deterministic scope.
thread_nondet_hits="$(scan_scope_hits 'std::thread::spawn\(|std::thread::sleep\(|tokio::spawn\(|tokio::time::sleep\(' "${DETERMINISM_RUNTIME_SCOPE[@]}" "${DETERMINISM_TEST_SCOPE[@]}")"
print_hits "error" "direct thread scheduling/timer calls in deterministic VM/simulation scope" "${thread_nondet_hits}" "Model scheduling and timers as explicit scheduler/effect inputs so replay behavior is controlled and cross-target equivalent."

echo ""
print_section "Summary"

echo "Errors:   ${errors}"
echo "Warnings: ${warnings}"
echo ""
printf "%-8s %-7s %s\n" "Severity" "Count" "Check"
printf "%-8s %-7s %s\n" "--------" "-----" "-----"
printf '%s' "${summary_lines}" | awk -F '\t' '{ printf "%-8s %-7s %s\n", $1, $3, $2 }'
echo ""

if [[ "${errors}" -gt 0 ]]; then
  echo -e "${RED}Rust architecture/style check failed:${NC} ${errors} error(s), ${warnings} warning(s)."
  exit 1
fi

if [[ "${warnings}" -gt 0 ]]; then
  echo -e "${YELLOW}Rust architecture/style check passed with warnings:${NC} ${warnings} warning(s)."
else
  echo -e "${GREEN}Rust architecture/style check passed.${NC}"
fi

exit 0
