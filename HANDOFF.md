# HANDOFF — 2026-08-13 (19b Slice 2 DONE — Refute consumption via
# rebuilt-literal equivalence transport + drop lane; next = Slice 3:
# isV0 gate lift + pd1/o139 acceptance → M3)

Read first: `DESIGN-endgame.md`, then `BOARD.md` — newest entries:
"nla-19b Slice 2 `done`" (the transport design + the '_tmp✝' trap +
the glue-subsumption finding), "nla-19b Slice 1 design review `done`".
Build system: Nix `lake` on PATH (not elan); full build green, WORKING
TREE CLEAN, everything committed.

**Source-of-truth rule: all ports cite `git show z3-4.12.5:<path>`
(repo `verus-cad/z3`), never the working tree.** Standing directive
(Danielle): cover ALL cases no matter how rare. z3-4.12.5 build for
differential probes: worktree `/tmp/z3-4.12.5` (`make -j shell`).

## State of the arc

**19b Slice 2 landed** (BOARD "nla-19b Slice 2 `done`"): the
pseudoDivision consumption gap (R7) is closed. Design: **rebuilt-
literal equivalence transport** — `SignRel`/`ZeroRel` inductives
(trusted, Check/Discharge.lean) relate a meta-reconstructed ORIGINAL
factor list to the rebuilt clause-visible atom position-by-position;
`holds_signRel`/`holds_zeroRel_eq` transport `Holds` across;
`Refute.pdRewriteLane` matches by value, re-proves the identity
(`pseudoDivisionIdentity`), takes lc evidence from the clause's own
A4/A5 literals (the new `FactKind.signPos` index + the diseq index),
re-extracts through the split `extractPosFacts`/`extractNegFacts`.
The const-remainder **drop lane** notes `f = 0` / `f ≠ 0` / definite
signs. Kind flips = the native σ-product (`oddSigProd` ~ z3's
`atom_sign`); payloads' lcSign/isEven/d-parity never trusted.

**New trusted lemma `pdSign_eq`** (parity-free zero-status) closed a
REAL Slice-1 family hole: z3 adds only `add_lc_diseq` for EQ-kind
rebuilds (:1181-1184), so d-odd sign-free-lc EQ cases had NO
applicable Slice-1 member.

**Glue-subsumption finding:** all Slice-0 pd drivers' arith members
also close STEP-FREE (nlinarith + eq×var lift + ineq×ineq pairing +
sq_nonneg subsume the transport on small cores) — pinned as
documentation; the lane's content is pinned by firing confirmations +
hint-flip pins. Watch at nla-16 whether harder instances need it.

## Next: 19b Slice 3 (gate lift + acceptance)

Spec is BOARD "nla-19b plan `boarded`" Slice 3 bullets:
- `isV0`/`Walk.precheck`: drop `pseudoDivision` from the reject set;
  `intBranch` stays gated (12e). The emission shapes per acceptance
  driver are already pinned (Slice-2 section = the census table).
- Acceptance: **pd1 AND o139 walked end-to-end** (o139 ✓ since the
  G11 session). pd1's bundles carry pseudoDivision — after the gate
  lift, regenerate the pd1 snapshot (scratch_dump.lean printer) into
  WalkTests and walk it.
- Negative probes per F-w; G5 row flips done; HANDOFF rewrite; M3
  declared per DESIGN-endgame tiers.

## Roadmap after 19b (unchanged)

12e (G6, integer B&B, 1–2 sessions, mostly solver-side) → nla-14 (the
`nonlinear_arith` tactic, 2–3 sessions; owns F-y; largest remaining
piece) → nla-15 (tactus wiring, ½) → nla-16 (parity harness, 1–2 +
findings; owns G8/G9/G10) = M6. Total-to-M6 ~6–10 sessions. Tier B
(G7 rootGeneric deg ≥ 3, S1 lane) deferred unless 16's harness shows
the corpus needs it. Q7: re-offer 11a (resultants) as the interleave
lane once 19b lands.

## Session mechanics + traps (cumulative; F3/F4 section of commit
d9d5df1 still accurate for dump/refresh recipes)

- **'_tmp✝' kernel free-variable errors are elaboration
  error-recovery artifacts** — an `unknown identifier` upstream (a
  missing def in a scratch) makes the elaborator synthesize junk that
  the kernel then reports as free variables. Grep for the REAL error
  first; do NOT chase the mvar table (an hour lost this session).
- `closeAlgRefl`/`closeNumerically`/`closeSigProd` now wrap their
  sandbox in `withoutModifyingState` (rolls the mvar table back over
  the ring/norm_num attempt — defense-in-depth for the Slice-1 hole
  class; success path unchanged, term extracted before rollback).
- Inductive PARAMETERS are implicit in constructors:
  `mkAppM ``SignRel.nil #[ρ]` is "too many explicit arguments" — use
  `mkAppOptM … #[some ρ]` (same for `List.nil`).
- `let mut` CANNOT be assigned inside a `withContext` closure —
  thread an explicit state record (the lane's `PdState`).
- A do-block `try` arm must end in a VALUE, not a bare assignment
  (`S := …` then `pure ()`).
- Structure-update syntax across a line break misparsed inside a
  nested `try` ("unexpected identifier; expected '}'" at the line
  end) — keep `{ S with … }` on one line.
- Inline `nlsat_arith_valid_steps #[…]` payloads with `(-1)` Int
  literals (or empty monomials) leave mvars at `evalExpr` — named
  `Array TraceStep` defs with ascriptions (the HANDOFF trap extends
  from `(-1), []` monomials to bare `(-1)` lcSign literals).
- Multi-example scratch files: Lean sorts diagnostics by position —
  logInfo instrumentation lines do NOT interleave with errors in
  temporal order; read by position.
- The earlier traps stand (block-buffered `--run` output; `lake
  build <module>` BEFORE `lake env lean scratch.lean`; swallowed
  try/catch instrumentation recipe; `Eq.mp` forward / `Eq.mpr`
  BACKWARD; `hasMVar` on produced terms; `(0:ℝ)` annotation;
  `Or.getAppFnArgs` = `#[A, B]`).

Commits this session: see `git log` (19b Slice 2 + pins + docs).
Memory file `verus-cad/memory/project_tactus_nonlinear_port.md`
updated (2026-08-13 Slice-2 entry; NEXT SESSION ORDER line current).
