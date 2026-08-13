## nla-29 `done` — anum arithmetic (eval/mul/inv/div) for the q≡0 fallbacks (Danielle, 2026-07-28; closed 2026-07-31)

**Design review (2026-07-31, post-close):** one F3-class fix landed
(mkBinary became-basic restore ordering — z3's destructor semantics mean
`mk_basic` sees the OVER-REFINED b on the a-path, and the b-path returns
the post-`mk_basic` a WITHOUT a final restore; first cut restored both
before re-dispatch. Judged nearly-unreachable in practice — getting a
cell below minMagnitude inside a mk_binary loop needs ~17 failed scans —
so no distinguishing pin; argued from source; suite re-green). Verified
clean against source: sign-variation zero-skip conventions identical
(:1895); deg-1 collapse is exact parity with z3's `set` (:481-487), not
a divergence; target-factor V ≥ 1 always (non-root-endpoint invariant
makes r_i's bracket strict) so the discard loop can never drop the
target — no infinite-loop corner; aux-z z-shadowing ≡ z3's ext_var2num
within the nested call; convert(x, i−1) truncation exact (:7718).

**Review follow-ups (Danielle's directives, 2026-07-31 — "nearly
unreachable still needs fixing"; "identical behavior in practice";
"cover all cases"; "prove the termination arguments"):** ALL LANDED.
(1) `evalCore`/`evalAnum` return `Option` — an unassigned variable is a
`none`, never the panic-default silent cell-0 read. (2) z3's throw
paths are `Option` too: `inv`/`div` of zero, `power` 0^0 — `none`
propagates (the faithful image of the exception unwinding out of the
nlsat call), replacing Lean's silent `1/0 = 0` / `0^0 = 1`; pins cover
the `none` cases. (3) `detBiv` is now Bareiss fraction-free (O(n³) poly
muls, exact over ℚ[x] at ANY matrix size) — first cut had a real bug
(skip-on-zero-entry dropped the pivot scaling; caught by the
composeXDivY pins); Laplace kept as the differential reference, pinned
equal on a specimen family. (4) Termination: the ops are now
non-recursive — became-basic is DATA (`MkBinaryResult`/`MkUnaryResult`
carrying the discovered rational; the caller re-dispatches through
`*RatL`/`*RatR` = `mk_basic` with a basic operand) instead of a
callback into the full op; `isolateRootsAt` split into
`isolateRootsAtCore` + `isolateRootsNested`/`isolateRootsAt`
(structural, no `partial`, the one-level nesting is now by
construction); `evalCore` has a real `termination_by x` (the variable
decreases; `maxSmallerThan` returns a proof-carrying subtype).
Remaining `partial` (analytic termination): **nla-31** below.
(5) CellStore lifts consolidated into `CellStore.lean` (which now
imports AnumArith); the `MkBinaryOps`/`MkUnaryOps` records are gone
(plain parameters). (6) eval-walker temp analysis agreed — recheck if
12c ever reuses temporaries across op calls.

