#!/usr/bin/env bash
# Sourced selection only: no compiler, cache server or process lifecycle.
case ${CACHE_FIXTURE_PREFIX:-AURA} in
  AURA|TELLTALE) cache_real_prefix=${CACHE_FIXTURE_PREFIX:-AURA} ;;
  *) echo 'unsupported cache fixture namespace' >&2; return 2 ;;
esac
cache_real_cargo_key=${cache_real_prefix}_NIX_CARGO_BIN
cache_real_clippy_key=${cache_real_prefix}_NIX_CLIPPY_BIN
cache_real_sccache_key=${cache_real_prefix}_NIX_SCCACHE_BIN
cache_real_optout_key=${cache_real_prefix}_NO_SCCACHE
: "${!cache_real_cargo_key:?}" "${!cache_real_clippy_key:?}" "${!cache_real_sccache_key:?}"
cache_real_cargo=${!cache_real_cargo_key}
cache_real_sccache=${!cache_real_sccache_key}
