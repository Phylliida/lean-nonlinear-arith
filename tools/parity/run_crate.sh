#!/usr/bin/env bash
# nla-16 parity runner — one crate, one backend, canonical flags.
#
# Usage:
#   run_crate.sh <crate> <z3|lean>
#
# Crate kinds are auto-detected:
#   - mirror (tactus-*, direct verus invocation on src/lib.rs),
#   - raw (verus-*, cargo-verus path).
# A lockfile serializes runs — the host rule is ≤4 threads TOTAL and a
# second concurrent run would blow it.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE="$(cd "$HERE/../../.." && pwd)"   # .../prog/verus-cad
REPO="$(cd "$HERE/../.." && pwd)"          # lean-nonlinear-arith
VERUS="$WORKSPACE/tactus/source/target-verus/release/verus"
LOCK=/tmp/nla16-parity.lock
LOGDIR="${NLA16_LOGDIR:-/tmp/nla16}"

[[ $# == 2 ]] || { echo "usage: $0 <crate> <z3|lean>" >&2; exit 2; }
crate="$1"; backend="$2"
mkdir -p "$LOGDIR"
log="$LOGDIR/${crate}-${backend}.log"

if ! mkdir "$LOCK" 2>/dev/null; then
  echo "another nla-16 run holds $LOCK (host ≤4-thread rule)" >&2
  exit 3
fi
trap 'rmdir "$LOCK"' EXIT

cdir="$WORKSPACE/$crate"
[[ -d "$cdir/src" ]] || { echo "no crate at $cdir" >&2; exit 2; }

if [[ -f "$cdir/Cargo.toml" && "$crate" == verus-* ]]; then
  # raw cargo path (dependency chain verifies too; per-crate reporting
  # takes the target crate's own run only)
  cargo_args=(verus verify --manifest-path "$cdir/Cargo.toml" -p "$crate")
  verus_args=(--num-threads 4)
  if [[ "$backend" == lean ]]; then
    export LEAN_PATH="$(cd "$WORKSPACE/tactus/lean-project" && lake env printenv LEAN_PATH)"
    export NLA16_STATS=1
    verus_args+=(--lean-backend)
  fi
  rustup run 1.94.0 env VERUS_ROOT="$WORKSPACE/tactus" \
    cargo "${cargo_args[@]}" -- "${verus_args[@]}" 2>&1 | tee "$log"
  rc=${PIPESTATUS[0]}
else
  # mirror path (direct verus; deps via export import/extern pairs are
  # per-mirror — mirrors in the pilot are dependency-free)
  args=(--num-threads 4 --crate-type=lib)
  if [[ "$backend" == lean ]]; then
    export LEAN_PATH="$(cd "$WORKSPACE/tactus/lean-project" && lake env printenv LEAN_PATH)"
    export NLA16_STATS=1
    args+=(--lean-backend)
  fi
  "$VERUS" "${args[@]}" "$cdir/src/lib.rs" 2>&1 | tee "$log"
  rc=${PIPESTATUS[0]}
fi
echo "[run_crate] log: $log (exit $rc)" >&2
exit "$rc"
