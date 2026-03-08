#!/usr/bin/env bash
set -euo pipefail

REPLACE_MODE=false
if [[ "${1:-}" == "--replace" ]]; then
  REPLACE_MODE=true
fi

if ! command -v git >/dev/null 2>&1; then
  echo "error: git is required" >&2
  exit 2
fi

if ! command -v grep >/dev/null 2>&1; then
  echo "error: grep is required" >&2
  exit 2
fi

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

if sed --version >/dev/null 2>&1; then
  SED_INPLACE="sed -i"
else
  SED_INPLACE="sed -i ''"
fi

found_any=false

echo "Scanning tracked files for emoji/symbol drift..."
echo

if [[ "$REPLACE_MODE" == true ]]; then
  check_count=0
  x_count=0
  warning_count=0

  while IFS= read -r file; do
    if [[ "$file" == "scripts/check/text-symbols.sh" ]]; then
      continue
    fi

    if [[ ! -f "$file" ]] || file "$file" | grep -q "binary"; then
      continue
    fi

    if grep -q '✅' "$file" 2>/dev/null; then
      count="$(grep -o '✅' "$file" | wc -l | tr -d ' ')"
      check_count=$((check_count + count))
      $SED_INPLACE 's/✅/✓/g' "$file"
      echo -e "${GREEN}Fixed${NC} $file: replaced $count ✅ -> ✓"
    fi

    if grep -q '❌' "$file" 2>/dev/null; then
      count="$(grep -o '❌' "$file" | wc -l | tr -d ' ')"
      x_count=$((x_count + count))
      $SED_INPLACE 's/❌/✗/g' "$file"
      echo -e "${GREEN}Fixed${NC} $file: replaced $count ❌ -> ✗"
    fi

    if grep -qP '⚠\x{FE0F}' "$file" 2>/dev/null; then
      count="$(grep -oP '⚠\x{FE0F}' "$file" | wc -l | tr -d ' ')"
      warning_count=$((warning_count + count))
      $SED_INPLACE $'s/⚠\xef\xb8\x8f/⚠/g' "$file"
      echo -e "${GREEN}Fixed${NC} $file: replaced $count ⚠️ -> ⚠"
    fi
  done < <(git ls-files)

  if [[ $check_count -gt 0 ]] || [[ $x_count -gt 0 ]] || [[ $warning_count -gt 0 ]]; then
    echo
    echo -e "${GREEN}Auto-fixed:${NC} $check_count ✅→✓, $x_count ❌→✗, $warning_count ⚠️→⚠"
    echo
  fi

  echo "Re-run scan for remaining symbols..."
  echo
fi

while IFS= read -r file; do
  if [[ "$file" == "scripts/check/text-symbols.sh" ]]; then
    continue
  fi

  if [[ ! -f "$file" ]] || file "$file" | grep -q "binary"; then
    continue
  fi

  if matches="$(grep -n -P '[\x{1F300}-\x{1F9FF}]|[\x{1FA00}-\x{1FAFF}]|✅|❌|⚠\x{FE0F}' "$file" 2>/dev/null)"; then
    found_any=true
    echo -e "${YELLOW}$file${NC}"
    echo "$matches" | while IFS= read -r line; do
      echo "  $line"
    done
    echo
  fi
done < <(git ls-files)

if [[ "$found_any" == false ]]; then
  echo -e "${GREEN}No disallowed emojis found in tracked files.${NC}"
else
  echo -e "${RED}Disallowed emojis found.${NC}"
  if [[ "$REPLACE_MODE" == false ]]; then
    echo -e "Run with ${YELLOW}--replace${NC} to normalize ✅→✓, ❌→✗, ⚠️→⚠."
  fi
  exit 1
fi
