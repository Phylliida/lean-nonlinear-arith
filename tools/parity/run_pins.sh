#!/usr/bin/env bash
# nla-16 stats-channel pins (Slice 0). Byte-exact stdout/stderr checks of
# the `[nla16-stats]` channel in both directions (armed / default-off).
# In-process env mutation is impossible on lean v4.25 (no IO.setEnv), so
# the pins run as subprocesses — that also exercises the END-TO-END shape
# the verus worker spawn relies on (env inherited by the lean child).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
cd "$REPO"

export LEAN_PATH="${LEAN_PATH:-$(lake env printenv LEAN_PATH)}"

fail() { echo "PIN FAILURE: $*" >&2; exit 1; }

out_l1="$(NLA16_STATS=1 lean "$HERE/pins/l1.lean" 2>&1)"
[[ "$out_l1" == *"warning: [nla16-stats] layer=1"* ]] \
  || fail "L1 armed pin: expected '[nla16-stats] layer=1', got: $out_l1"

out_l2="$(NLA16_STATS=1 lean "$HERE/pins/l2.lean" 2>&1)"
[[ "$out_l2" == *"warning: [nla16-stats] layer=2 conflicts=1"* ]] \
  || fail "L2 armed pin: expected '[nla16-stats] layer=2 conflicts=1', got: $out_l2"

# exact payload (nothing else)
grep -q "warning: \[nla16-stats\] layer=1$" <<<"$out_l1" \
  || fail "L1 armed pin carries unexpected extra text: $out_l1"
! grep -q "error" <<<"$out_l1" || fail "L1 armed pin produced an error: $out_l1"
! grep -q "error" <<<"$out_l2" || fail "L2 armed pin produced an error: $out_l2"

out_off="$(lean "$HERE/pins/l1.lean" 2>&1)"
[[ -z "$out_off" ]] || fail "default-off pin: expected silence, got: $out_off"

# wrong-value gate (NLA16_STATS present but not "1" must stay silent —
# POSIX has no set-via-unset; the gate is on the value, documented on
# reportStats)
out_zero="$(NLA16_STATS=0 lean "$HERE/pins/l1.lean" 2>&1)"
[[ -z "$out_zero" ]] || fail "value-gate pin: NLA16_STATS=0 must be silent, got: $out_zero"

echo "stats-channel pins: OK (l1/l2 armed, default-off, value-gate)"
