## nla-12d design review `done` (2026-08-01, Danielle-requested, post-12d.6a)

Method: the standing one — adversarial re-read of
`git show z3-4.12.5:src/nlsat/nlsat_explain.{h,cpp}` (+ polynomial.cpp
gcd/factor/psc pieces, nlsat_solver del/reorder) against the port,
hunting divergences and regrettable decisions.

**ONE FIX LANDED:** `addCellLits` read y's value with `.get!` — on an
unassigned y that is a panic-returns-default (silently reads cell 0 =
wrong value, F7 class). z3 SASSERTs assigned; release reads an
uninitialized anum (no behavior to match). Fixed to the abort image
(`none`) + pin.

**VERIFIED CLEAN (source re-read):** the uniModGcd constant-image
quirk's INERTNESS on our paths (every consumer treats a const gcd as
"const" — Yun's is_const branch, iccp's is_const→mk_one; the value is
never observed); simplifyLit keep-original counts as UNMODIFIED (z3
compares `l == new_lit` — pinned); simplifyCore's lower-stage
!modified → re-select loop risk is UNREACHABLE post-normalize
(normalize eliminates every lower-stage factor first, so the eq's own
atom never survives into simplify — z3's VERIFY is correct by
construction; only direct non-pipeline calls could hit it);
simplifyLit's `value(newL)` none-branch (takes z3's
value-≠-l_true path; a genuine evaluator abort is unreachable in
explain's context — all stage vars assigned, z3 SASSERTs the same);
addLiteral's release-kept true_literal (never emitted: all atom
creation goes through fresh-bvar mkIneqAtom/mkRootAtom);
Explain.explain's fresh per-call state (z3's buffers are perf-reuse
only); explainCache keys are assignment-independent (factor/psc are
pure poly functions; reset at reorder is hooked).

**REGISTERED, WATCHED (no action needed):**
- mod_gcd_rec livelock when `lc_g ≡ 0` (both substituted pp's zero at
  the sample) — z3 has the SAME infinite loop (peek_fresh inner while,
  :4174-4181); faithful; termination territory (nla-31).
- peek_fresh counter-based (registered output-independence argument;
  z3's libc-rand sequence is platform-dependent anyway). Verified:
  interpolation target is a fixed polynomial (lc_g·monic-gcd image),
  so samples/skeletons/results are sequence-independent once
  divides-verified.
- select_eq d=0 (release semantics, debug SASSERT only).
- elimVanishing's literal k==0 branch is defensive-dead upstream
  (zero reduct is caught by is_const first) — ported verbatim.
- selectLowerStageEq/simplifyLit Option-free spots where z3's
  behavior on its own throw is a crash (no behavior to match).

**HYGIENE NOTES (non-blocking):** project()'s local `todo` mirror
variable could desync from state on future edits (read state
directly); `x.getD 0` in the project loop hides an invariant the
match already guarantees.

