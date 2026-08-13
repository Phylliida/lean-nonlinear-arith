# HANDOFF — 2026-08-13 (19b Slice 1 DONE — grammar + identity +
# sign-transfer; closeAlgRefl HOLE fixed; next = Slice 2: Refute
# rebuilt-literal consumption)

Read first: `DESIGN-endgame.md`, then `BOARD.md` — newest entries:
"nla-19b plan `boarded`" (4 slices), "nla-19b Slice 0 `done`" +
addendum (the writeback bug), **"G11 lane `done` + o139 walked
END-TO-END"**. Build system: Nix `lake` on PATH (not elan); full
build green at 7612 jobs, WORKING TREE CLEAN, everything committed.

**Source-of-truth rule: all ports cite `git show z3-4.12.5:<path>`
(repo `verus-cad/z3`), never the working tree.** Standing directive
(Danielle): cover ALL cases no matter how rare. z3-4.12.5 build for
differential probes: worktree `/tmp/z3-4.12.5` (`make -j shell`).

## State of the arc

**o139 (ordering_139 raw-form, 6 vars) is fully walked** — all 6
learned cids + final bundle, exactly z3-4.12.5's 6-conflict DAG,
kernel-checked. The walk's richest real refutation: rootGeneric deg-1
non-const-lc (G11, production-first), cellBound/linearRoot
cross-links, factorSplit bundles, pure-resolution nodes, all six
input clauses referenced. This is HALF of 19b Slice 3's acceptance
("pd1 AND o139 walked"); pd1 is gated on Slices 1–2.

**G11 lane (this session's close-out of the broken tree):**
`negRootDeg1Produce` had parse errors + 3 latent runtime bugs (Or
args off-by-one; the `linearNonconst_aux` route's `S *` mismatch —
replaced with the sign-matched
`linearRootNonconst{Pos,Neg}_discharge` + `Iff.not` route;
`mkCoeFactEq`'s list-get redex RHS stalling the mangle — pinned with
`mkExpectedTypeHint`). Full bug list + the `Eq.mp`-forward /
`Eq.mpr`-BACKWARD red herring: BOARD "G11 lane `done`" entry.
Pins: RefuteTests G11 section (cid7 ±steps, cid8 ±steps, cid9
±steps, cid9-minus-root-literal rejects). WalkTests o139 example
builds.

## Next: 19b Slice 2 (Refute rebuilt-literal consumption — the risk item)

Slice 1 is DONE (BOARD "nla-19b Slice 1 `done`"): grammar +
`pseudoDivisionIdentity` + the 15-theorem sign-transfer family landed,
plus the closeAlgRefl HOLE fix (`hasMVar`, not `isAssigned`, at every
term-producing close site).

Spec is the BOARD "nla-19b plan `boarded`" entry, Slice 2 bullets +
the Slice-1 entry's carried notes:
- `collectStepFacts` pseudoDivision lane: match clause literals
  against step payloads by value (rebuilt literal's factor list pairs
  with per-step `(f, r)` payloads; `coeffsOfValue` reducer family for
  matching evidence).
- Per matched rewrite: note the identity (`pseudoDivisionIdentity`,
  sandboxed close) + `lc ≠ 0` (from the A5 diseq clause literal, or
  decide-grade when lc is const) + the sign fact on f from the sign
  fact on r via the parity lemmas (`pdSign_{even,odd_pos,odd_neg}_*`).
- The A3 decode table for rebuilt literals (kind, neg vs factor-list),
  pinned per shape with corruption probes in the F-w pattern
  (grammar-breaking vs grammar-clean-semantic-mismatch lanes).
- Path (c) keep-original tolerance: unmatched pseudoDivision steps
  contribute nothing (pin with a fixture).
- R-h: the A5 diseq enters proj as `⟨6,false⟩` (the EQ atom
  unnegated) — pin the exact assumption-literal polarity convention
  for EQ-kind lc assumptions at the F2 seam.
- Fuel: rebuilt-literal path-fanout bounded per literal like the
  review-11 fix (clause-sized, never a hardcoded constant).

Then **Slice 3** (isV0 gate lift for pseudoDivision only — intBranch
stays gated → 12e; pin which emission shapes each acceptance driver
emits BEFORE lifting; acceptance = pd1 walked end-to-end; G5 flips
done; M3 declared per DESIGN-endgame tiers).

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

- Full `lean --run` output is BLOCK-BUFFERED when redirected — flush
  between drivers or use separate files.
- `lake env lean scratch.lean` does NOT rebuild the library — `lake
  build <module>` FIRST, then run the scratch (stale .olean silently
  hides edits; bit this session).
- The lane `try/catch` discipline SWALLOWS runtime throws — when a
  lane "does nothing", instrument the catch with `logInfo` FIRST
  (this session's cid-9 debug method; revert after).
- `Eq.mp`/`Eq.mpr` are NOT the same direction: mp = forward (α→β),
  mpr = BACKWARD (β→α). Check core signatures before "fixing" a
  transport direction (two wasted iterations this session).
- `proveByRefl`'s refl term has the INTRINSIC type `a = a`, not the
  ascribed `a = b` — pin with `mkExpectedTypeHint` when the endpoint
  spelling matters downstream (simp/mangle).
- Disjunction lemmas' sign CONJUNCTS are accessor-spelled
  (`evalP ρ (coeffsOf …)[k]!`); the redex stalls the mangle's evalP
  unfold and the dead-end split leaf dies ON that conjunct — transport
  to the concrete spelling at note time (`mkSignTransports`,
  review F-ii). The leaf-dump recipe: temporarily log the lctx in
  `closeWithSplits`' failure arm.
- Inline step payloads in `nlsat_arith_valid_steps #[…]` with empty
  monomials (`(-1), []`) leave metavariables at `evalExpr` — use
  named `MPoly` defs (type ascription guides elaboration).
- Tactic-close-and-check sites must check the produced TERM for holes
  (`hasMVar` on the instantiated term), not the mvar for assignedness:
  `ring`/`norm_num` assign the goal with their normalization chain
  BEFORE the final close, so a failure can leave an assigned-but-holed
  term while only logging the error (the closeAlgRefl HOLE, 19b
  Slice 1). Kernel rejects holed terms downstream, but the clean skip
  discipline needs the throw at the close site.
- `(0:ℝ)` annotation required in Statements with accessor subterms
  (the ↑0 cast trap — hit twice). `getAppFnArgs` on `Or A B` gives
  `#[A, B]` (head excluded).
- Nothing matches on `match … | pat | guard =>` — guards are nested
  `if`s. z3's `todo_set` in_set is current-contents-only. nlinarith
  can't multiply an equality by a free variable (the eq×var lift is
  the house answer). `read_file` tool flaked on `Check/Semantics.lean`
  (binary-detect; use sed/grep).

Commits this session: see `git log` (G11 close-out + pins + docs).
Memory file `verus-cad/memory/project_tactus_nonlinear_port.md`
updated (both 2026-08-10 and 2026-08-11 entries; NEXT SESSION ORDER
line current).
