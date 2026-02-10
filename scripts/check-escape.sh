#!/usr/bin/env bash
#
# check-escape.sh
#
# Searches the Lean4 codebase for escape hatches that bypass verification.
# Returns results organized by type with file paths and line numbers.
#
# Escape hatches checked:
#   Critical: sorry, sorryAx, axiom, private axiom, lcProof, decreasing_by sorry
#   High:     unsafe, partial def, @[csimp], unsafeCast, panic!, unreachable!
#   Medium:   native_decide, implemented_by, extern, reduceBool, reduceNat
#   Low:      opaque, noncomputable

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_ROOT="${SCRIPT_DIR}/../lean"

# Colors for output
RED='\033[0;31m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
GREEN='\033[0;32m'
NC='\033[0m'
BOLD='\033[1m'

TOTAL=0

print_header() {
    echo ""
    echo -e "${BOLD}${BLUE}═══════════════════════════════════════════════════════════════${NC}"
    echo -e "${BOLD}${BLUE}  Lean4 Escape Hatch Report${NC}"
    echo -e "${BOLD}${BLUE}═══════════════════════════════════════════════════════════════${NC}"
    echo ""
}

search_pattern() {
    local pattern="$1"
    local description="$2"
    local severity="$3"
    local color

    case "$severity" in
        critical) color="$RED" ;;
        high)     color="$YELLOW" ;;
        medium)   color="$BLUE" ;;
        low)      color="$GREEN" ;;
        *)        color="$NC" ;;
    esac

    # Find matches, excluding .lake and target directories
    local results
    results=$(grep -rn --include="*.lean" -E "$pattern" "$LEAN_ROOT" 2>/dev/null | \
              grep -v "/\.lake/" | \
              grep -v "/target/" | \
              grep -v "scripts/check-escape" || true)

    if [[ -n "$results" ]]; then
        local count
        count=$(echo "$results" | wc -l | tr -d ' ')

        echo -e "${BOLD}${color}────────────────────────────────────────────────────────────────${NC}"
        echo -e "${BOLD}${color}  ${description}${NC}"
        printf "${BOLD}${color}  Pattern: %s  |  Severity: %s  |  Count: %s${NC}\n" "$pattern" "$severity" "$count"
        echo -e "${BOLD}${color}────────────────────────────────────────────────────────────────${NC}"

        echo "$results" | while IFS= read -r line; do
            # Make path relative to LEAN_ROOT
            local rel_path="${line#$LEAN_ROOT/}"
            echo "  $rel_path"
        done

        echo ""
        TOTAL=$((TOTAL + count))
        echo "$count" >> /tmp/escape_hatch_counts_$$
    fi
}

main() {
    # Clean up temp file
    rm -f /tmp/escape_hatch_counts_$$

    print_header

    # Critical severity - these bypass proofs entirely
    search_pattern "\\bsorry\\b" "Admits goal without proof" "critical"
    search_pattern "sorryAx" "Sorry axiom (shows in #print axioms)" "critical"
    search_pattern "^[[:space:]]*axiom\\b" "Introduces unproven assumption" "critical"
    search_pattern "^[[:space:]]*private[[:space:]]+axiom\\b" "Private axiom (hidden unproven assumption)" "critical"
    search_pattern "lcProof" "Low-level proof bypass (unsafe axiom)" "critical"
    search_pattern "decreasing_by[[:space:]]+sorry" "Unproved termination" "critical"

    # High severity - these disable key checks
    search_pattern "\\bunsafe\\b" "Disables safety checks" "high"
    search_pattern "^[[:space:]]*partial[[:space:]]+def\\b" "Disables termination checking" "high"
    search_pattern "@\\[csimp\\]" "Can smuggle axioms into proofs" "high"
    search_pattern "unsafeCast" "Unchecked type cast" "high"
    search_pattern "\\bpanic!\\b" "Runtime crash (can mask bugs)" "high"
    search_pattern "\\bunreachable!\\b" "Asserts unreachability" "high"

    # Medium severity - these use native code (depend on compiler correctness)
    search_pattern "native_decide" "Uses native code for decidability" "medium"
    search_pattern "implemented_by" "Replaces with native implementation" "medium"
    search_pattern "\\bextern\\b" "Foreign function interface" "medium"
    search_pattern "Lean\\.reduceBool" "Native boolean reduction" "medium"
    search_pattern "Lean\\.reduceNat" "Native natural number reduction" "medium"

    # Low severity - worth tracking
    search_pattern "\\bopaque\\b" "Hides implementation details" "low"
    search_pattern "\\bnoncomputable\\b" "Non-computable definition" "low"

    # Calculate total from temp file
    if [[ -f /tmp/escape_hatch_counts_$$ ]]; then
        TOTAL=$(awk '{s+=$1} END {print s}' /tmp/escape_hatch_counts_$$)
        rm -f /tmp/escape_hatch_counts_$$
    fi

    # Summary
    echo -e "${BOLD}${BLUE}═══════════════════════════════════════════════════════════════${NC}"
    echo -e "${BOLD}${BLUE}  Summary: ${TOTAL} escape hatch(es) found${NC}"
    echo -e "${BOLD}${BLUE}═══════════════════════════════════════════════════════════════${NC}"

    if [[ $TOTAL -eq 0 ]]; then
        echo -e "${GREEN}${BOLD}  ✓ No escape hatches found. Proofs are complete.${NC}"
    else
        echo -e "${YELLOW}${BOLD}  ⚠ Review escape hatches before claiming results.${NC}"
    fi
    echo ""
}

main "$@"
