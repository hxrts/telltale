#!/usr/bin/env bash
set -euo pipefail

# Rust Style Guide Conformance Checker for Telltale-Aura
# Based on work/style_guide_rust.md
#
# Usage:
#   ./scripts/lint-check.sh          # Full check
#   ./scripts/lint-check.sh --quick  # Quick check (format + clippy only)

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

ERRORS=0
WARNINGS=0
QUICK_MODE=false

# Parse arguments
for arg in "$@"; do
    case $arg in
        --quick)
            QUICK_MODE=true
            shift
            ;;
    esac
done

log_error() { echo -e "${RED}ERROR:${NC} $1"; ((ERRORS++)) || true; }
log_warn() { echo -e "${YELLOW}WARN:${NC} $1"; ((WARNINGS++)) || true; }
log_ok() { echo -e "${GREEN}OK:${NC} $1"; }
log_info() { echo -e "${BLUE}INFO:${NC} $1"; }
section() { echo -e "\n${BLUE}--- $1 ---${NC}"; }

echo "========================================"
echo "  Rust Style Guide Conformance Check"
echo "  See: work/style_guide_rust.md"
echo "========================================"

if $QUICK_MODE; then
    log_info "Running in quick mode (format + clippy only)"
fi

# 1. Rustfmt check
section "Checking formatting"
if cargo fmt --all -- --check 2>/dev/null; then
    log_ok "Code is properly formatted"
else
    log_error "Code formatting issues found. Run 'cargo fmt --all'"
fi

# 2. Clippy with strict settings
section "Running clippy (strict)"
CLIPPY_FLAGS=(
    -D warnings
    -D clippy::let_underscore_must_use
    -D clippy::missing_safety_doc
    -W clippy::missing_errors_doc
    -W clippy::missing_panics_doc
    -W clippy::cognitive_complexity
    -W clippy::too_many_arguments
    -W clippy::too_many_lines
    -W clippy::fn_params_excessive_bools
    -W clippy::as_conversions
    -W clippy::cast_possible_truncation
    -W clippy::large_stack_arrays
    -W clippy::inefficient_to_string
    -W clippy::must_use_candidate
)

if cargo clippy --workspace --all-targets --all-features -- "${CLIPPY_FLAGS[@]}" 2>&1; then
    log_ok "Clippy passed"
else
    log_error "Clippy found issues"
fi

# Exit early in quick mode
if $QUICK_MODE; then
    echo ""
    echo "========================================"
    echo "  Quick Check Summary"
    echo "========================================"
    echo -e "Errors:   ${RED}$ERRORS${NC}"
    echo -e "Warnings: ${YELLOW}$WARNINGS${NC}"
    exit $( [ "$ERRORS" -gt 0 ] && echo 1 || echo 0 )
fi

# 3. Check for unsafe code outside designated modules
section "Checking unsafe usage"
UNSAFE_FILES=$(grep -rl "unsafe" rust/*/src --include="*.rs" 2>/dev/null || true)
UNSAFE_WITHOUT_SAFETY=0

for file in $UNSAFE_FILES; do
    # Check if file has unsafe without Safety comment nearby
    if grep -q "unsafe {" "$file" 2>/dev/null; then
        if ! grep -B2 "unsafe {" "$file" | grep -q "// Safety:"; then
            ((UNSAFE_WITHOUT_SAFETY++)) || true
            log_warn "Unsafe block without Safety comment: $file"
        fi
    fi
done

if [ "$UNSAFE_WITHOUT_SAFETY" -eq 0 ]; then
    log_ok "All unsafe blocks have Safety comments"
fi

# 4. Check for unbounded loops (style guide: put a limit on everything)
section "Checking for unbounded loops"
UNBOUNDED_LOOPS=$(grep -rn "loop {" rust/*/src --include="*.rs" 2>/dev/null \
    | grep -v "// bounded\|// forever\|// infinite\|#\[allow" \
    | wc -l | tr -d ' ')

if [ "$UNBOUNDED_LOOPS" -gt 0 ]; then
    log_warn "Found $UNBOUNDED_LOOPS potential unbounded loops"
    echo "  Add '// bounded:' or '// forever:' comment to document intent"
    grep -rn "loop {" rust/*/src --include="*.rs" 2>/dev/null \
        | grep -v "// bounded\|// forever\|// infinite\|#\[allow" \
        | head -5
else
    log_ok "All loops are documented or bounded"
fi

# 5. Check for usize in stored/serialized types (style guide: explicit sizes)
section "Checking for usize in serializable types"
USIZE_SERDE=$(grep -rn "usize" rust/*/src --include="*.rs" 2>/dev/null \
    | grep -E "Serialize|Deserialize" \
    | wc -l | tr -d ' ')

if [ "$USIZE_SERDE" -gt 0 ]; then
    log_warn "Found $USIZE_SERDE files with usize near Serialize/Deserialize"
    echo "  Consider using explicit u32/u64 for serialized data"
else
    log_ok "No usize in serializable types"
fi

# 6. Check for TODO/FIXME comments (technical debt tracking)
section "Checking for technical debt markers"
TODO_COUNT=$(grep -rn "TODO\|FIXME\|HACK\|XXX" rust/*/src --include="*.rs" 2>/dev/null | wc -l | tr -d ' ')

if [ "$TODO_COUNT" -gt 0 ]; then
    log_info "Found $TODO_COUNT TODO/FIXME comments (technical debt)"
    grep -rn "TODO\|FIXME" rust/*/src --include="*.rs" 2>/dev/null | head -5 || true
else
    log_ok "No technical debt markers found"
fi

# 7. Check for magic numbers in bounds (style guide: encode limits as constants)
section "Checking for magic numbers"
MAGIC_BOUNDS=$(grep -rn "< [0-9]\{3,\}\|> [0-9]\{3,\}\|<= [0-9]\{3,\}\|>= [0-9]\{3,\}" \
    rust/*/src --include="*.rs" 2>/dev/null \
    | grep -v "const\|static\|test\|#\[" \
    | wc -l | tr -d ' ')

if [ "$MAGIC_BOUNDS" -gt 0 ]; then
    log_warn "Found $MAGIC_BOUNDS potential magic numbers (3+ digits) in comparisons"
    echo "  Consider extracting to named constants with units (e.g., MAX_BATCH_SIZE)"
else
    log_ok "No magic numbers in bounds"
fi

# 8. Check for #[must_use] candidates
section "Checking for #[must_use] candidates"
MUST_USE_OUTPUT=$(cargo clippy --workspace --all-features -- -W clippy::must_use_candidate 2>&1 || true)
MUST_USE_COUNT=$(echo "$MUST_USE_OUTPUT" | grep -c "must_use_candidate" || true)

if [ "$MUST_USE_COUNT" -gt 10 ]; then
    log_warn "$MUST_USE_COUNT functions could benefit from #[must_use]"
else
    log_ok "Most return values are properly annotated"
fi

# 9. Check for large enums (performance consideration)
section "Checking for large enum variants"
LARGE_ENUM_OUTPUT=$(cargo clippy --workspace --all-features -- -W clippy::large_enum_variant 2>&1 || true)
LARGE_ENUM_COUNT=$(echo "$LARGE_ENUM_OUTPUT" | grep -c "large_enum_variant" || true)

if [ "$LARGE_ENUM_COUNT" -gt 0 ]; then
    log_warn "$LARGE_ENUM_COUNT large enum variants found"
    echo "  Consider boxing large variants"
else
    log_ok "No problematic large enum variants"
fi

# 10. Run cargo deny for dependency audit (if available)
section "Checking dependencies"
if command -v cargo-deny &> /dev/null; then
    if cargo deny check 2>&1; then
        log_ok "Dependency audit passed"
    else
        log_warn "Dependency audit found issues"
    fi
else
    log_info "cargo-deny not installed. Run: cargo install cargo-deny"
fi

# 11. Check test coverage (informational)
section "Test information"
TEST_COUNT=$(cargo test --workspace --all-features -- --list 2>/dev/null | grep -c "test$" || echo "0")
log_info "Found $TEST_COUNT tests in workspace"

# Summary
echo ""
echo "========================================"
echo "  Summary"
echo "========================================"
echo -e "Errors:   ${RED}$ERRORS${NC}"
echo -e "Warnings: ${YELLOW}$WARNINGS${NC}"

if [ "$ERRORS" -gt 0 ]; then
    echo ""
    echo -e "${RED}Fix errors before committing${NC}"
    exit 1
elif [ "$WARNINGS" -gt 10 ]; then
    echo ""
    echo -e "${YELLOW}Consider addressing warnings${NC}"
    exit 0
else
    echo ""
    echo -e "${GREEN}All checks passed!${NC}"
    exit 0
fi
