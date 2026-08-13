## nla-19a design review 5 `done` (2026-08-07, pre-F2-step-collection; probe-driven; decisions resolved by Danielle's principle-delegation same day)

Method: adversarial re-read of
`git show z3-4.12.5:src/nlsat/nlsat_explain.cpp` (:700-:1000 —
add_root_literal chain, mk_linear/mk_quadratic/mk_plinear_root,
ensure_sign, add_cell_lits) against the F2 step-fact-collection recipe
in the HANDOFF, PLUS a five-probe empirical campaign (the phantom-bug
lesson applied: verify the decode against the raw dump BEFORE building
machinery). Decisions: Danielle's reply to the review's R-a..R-d/Q-i
was principle-delegation ("I just use the principles I described at the
start") — each resolved below by the standing three (right-way / z3
fidelity / prove-over-empiricism).

**VERIFIED CLEAN (source re-read):**
- **V-a (cellBound pairing):** `add_cell_lits` calls `add_root_literal`
  per bound (exact-hit ROOT_EQ early return; single lower and/or upper,
  tightest-root scan). Every `cellBound` trace step is therefore paired
  with an immediately-preceding encoding step from the same
  `add_root_literal` call — the R-iv accumulation shape is confirmed,
  and R5 redundancy holds structurally: for deg ≤ 2 the encoding
  (linear/thom/generic) always puts its literal(s) in the clause, so
  the cellBound step adds no fact the encoding didn't.
- **V-b (mk_quadratic_root emission order):** disc `ensure_sign` FIRST
  on the RAW `q = B²−4AC` (NOT normalized), then A, then the `sa = 0`
  degenerate reroute to `mk_plinear_root(B·y+C)` (q RAW), then
  `ensure_sign(p_diff)` on the `managerNormalize`'d `2Ay+B`, then
  `ensure_sign(p)` only when `sq > 0`. Matches the Trace.lean grammar
  + the R-ii decoder reconstruction surfaces (review 4, V-v).
- **V-c (const sign-skip):** `ensure_sign` adds NO literal for const
  polys (is_const skip :845) — bundle 7's A=1/disc=8 leave no atoms
  (matches the dump); const sign facts are decide-grade per E1.
- **V-d (polarity chain fully inside the discharge):** the assumption
  literal `add_simple_assumption` emits IS the clause literal (explain's
  m_result flows into the lemma unnegated; only core literals are
  negated at `resolve_lazy_justification` — V-i of review 4). So
  clause-literal-fails ≡ `¬ SHolds ρ emitted.1 emitted.2` definitionally,
  and the whole LE/GE kind-remap + negation fold lives inside
  `linearRoot_discharge`. The F2 elaborator needs NO polarity logic of
  its own. Hand-verified on the GT case.
- **V-e (decode validity check):** `arithClause = proj ++ ¬core` is the
  ONLY valid reading — with core un-negated the dump's arith clauses
  are falsifiable (hand countermodels). The HANDOFF's English
  transcription of bundles 6/7 used the INVALID reading; the raw dump
  data and Assemble.lean were right all along.

**FINDINGS:**
- **F-i (the big one, probe-verified): the acceptance driver's ENTIRE
  F2 layer closes under the F2 skeleton + a glue upgrade, with ZERO
  step-fact collection.** The HANDOFF's "step facts load-bearing for
  bundles 6/7" prediction was FALSE — traced to the invalid core-
  polarity transcription (the phantom-bug class, third occurrence).
  RootCmp facts are never the obstruction for these bundles: the
  encoding literals sit in the clause, so their failures deliver the
  sign facts directly. (Deeper reason, recorded for the census: Thom/
  linear encodings make root comparisons first-order in the signs, so
  the contradiction is sign-level whenever the encoding literals are
  present.) Probe data: bundle 6 closes by nlinarith on products of the
  bound failures; bundle 7 needs the eq-fact substitution (ρ0=1) which
  nlinarith reaches via the (t≥0)(1−t≥0) self-product once normalized;
  final core 2 is the only non-obvious one (disequality).
- **F-ii (the ACTUAL glue gaps, both diagnosed by probe, both FIXED in
  `Refute.lean` same day):** (a) NORMALIZATION — the evalP simp-unfold
  leaves `ρ x ^ 1` powers and `↑(-1)` Int-cast numerals in spellings
  linarith fails on (even though pp-identical hand-written contexts
  close — root cause inside linarith's preprocessing NOT identified in
  the bounded look; recorded as an open trap, mdata hypothesis noted);
  fix = `ring_nf at *` after the simp-unfold, principled regardless
  (ring_nf IS the linarith-normalizer). (b) DISEQUALITIES — `¬(t = 0)`
  facts (¬core on EQ atoms, e.g. final core 2's) are invisible to
  linarith/nlinarith; fix = lazy trichotomy splits (`lt_or_gt_of_ne` +
  `MVarId.cases`, one diseq at a time, glue retried per branch, split
  de-dup by fvarId, fuel 8). Soundness untouched: splits only add
  classical consequences; failure stays rejection.
- **F-iii (re-scope, R-a resolved by principle):** step-fact collection
  (Coverage-theorem consumption) is OFF the acceptance driver's
  critical path. It remains required for the accept-⊇-grammar contract
  (R-viii) for clause shapes whose contradiction is NOT literal-local —
  the identified case is `rootGeneric` (no encoding literals exist; the
  root atom's failure gives `rootCmp ∧ i ≤ rootCount` DEFINITIONALLY
  via an `extractFact` extension, but the contradiction itself — e.g.
  definite-disc `rootCount = 0` — needs per-shape generation).
  Re-sequenced: land glue + F3 + F4 first; step-fact collection becomes
  its own slice driven by a GRAMMAR-COVERAGE CENSUS (enumerate grammar
  shapes × clause-locality), which is the Q1/E2 pattern applied to F2 —
  prove-over-empiricism without building against a falsified prediction.
- **F-iv (review-4 carry-over, still open):** `extractFact` matches
  only single-factor `(q, false)` atoms; the A1 multi-factor ¬EQ
  collapse (V-iv's named helper) and even-parity variants remain
  grammar-completeness gaps (not exercised by the driver). Folded into
  the census slice.

**DECISIONS (by principle-delegation):**
- **R-a:** glue upgrade IS the F2 completion for the acceptance driver;
  step-fact collection re-sequenced per F-iii.
- **R-b:** bounded root-cause look at the linarith normalization gap
  done (open trap recorded); ring_nf-first stands on its own merits.
- **R-c:** probe files absorbed — pipeline landed in `Refute.lean`, the
  five driver clauses + negative probe pinned in `RefuteTests.lean`,
  scratch deleted.
- **R-d:** F3 (DAG walk) next, unchanged — nothing in the findings
  touches its design (per-cid fold, `upRefutes … by decide` per R-v,
  final-bundle target `[]`, `clauseSatI_interp` bridge, R-vi contract).
- **Q-i:** no separate literal-locality formalization project (the
  strong version is an nlinarith-completeness claim — not formalizable);
  the provable per-shape version folds into the census slice.

**New traps (cost class noted):**
- `#guard_msgs (drop error)` takes the command's DOCSTRING as the
  expected message — rejection probes must use plain `/- -/` comments,
  never `/-- -/`.
- `replaceMainGoal` THROWS on an empty goal list ("No goals to be
  solved") — after closing a branch the list is empty; use `setGoals`
  for explicit goal management in meta glue.
- `List Literal` has no `ToMessageData` — repr-map for error messages.
- linarith can fail on contexts PP-IDENTICAL to closing ones (post-simp
  spellings) — normalize with `ring_nf` after evalP simp-unfolds before
  any linarith/nlinarith glue; do not trust the display. (Root cause
  open; bounded investigation per R-b.)
- Phantom-bug re-confirmation (third occurrence): the HANDOFF's English
  transcription of the dump's arith clauses silently used the
  un-negated core — an INVALID reading that predicted spurious
  machinery. Verify decodes against the raw dump/`arithClause` def
  before designing against them.

**F2 status after landing:** glue upgrade in `Refute.lean` (ring_nf +
lazy diseq splits); driver pins 5 + negative probe in `RefuteTests.lean`
(joining the 4 + 1 x0²+x1²<0 pins); full build green 7608 jobs.
NEXT: F3 DAG walk (per HANDOFF), then F4 acceptance (now unblocked —
all the driver's arith lemmas are already pinned), F5, then the
grammar-coverage census slice (step-fact collection + F-iv).

**F3 DONE (2026-08-09): the DAG walk `nlsat_refute`**
(`Nlsat/Walk.lean` + `WalkTests.lean`, build green 7610). Contract
(R-vi): goal `∀ ρ, (∀ C ∈ Cs, clauseHolds ρ atoms C) → False` where
`Cs` = the referenced input clauses' lits in increasing cid order
(walk-computed from the snapshot; the true-bvar unit is never
referenced — it is undecodable by construction); tactic arg = the
`s.refutation` payload. Per learned cid (increasing): F-set from
`resolution` markers (input → bridged hypothesis via the new
`clauseSatI_interp` path, learned → earlier fold result, `.arith` → F2
`proveClauseSat` in a sandboxed sub-goal); `.decision` skipped;
non-resolution steps contribute nothing at this layer (review 5 F-i).
RUP per node by `decide` (never native_decide; Nat/Bool-only values) +
`upRefutes_sound`; final bundle's empty lemma closes `False`. Pins:
end-to-end walks of BOTH live refutations (sq x0²+x1²<0: 3 learned +
final; the 2-var driver: 2 learned + final — the full F2 arith chain
exercised in-walk) + 3 negative probes (input-list mismatch, corrupted
arith polarity [rejects at precheck RUP — the propositional chain
breaks first], corrupted lemma [intended RUP failure]). Snapshot test
data is MACHINE-GENERATED by `scratch_dump.lean` (dump + Lean-literal
printer; no hand transcription — phantom-bug discipline).
New trusted helpers in Assemble.lean: `not_litSatI_forall_of_not_clauseSatI`,
`clauseDecodable` + `clauseDecodable_true` (per-clause decodability as a
kernel-computable Bool check — sidesteps quoting Atom witnesses and
getElem? construction entirely; enters proofs as `by decide`).
**New traps:** (1) **`Meta.evalExpr` of a bare FUNCTION const
mis-evaluates on this toolchain** (v4.25.0 Nix): `isV0` came back
`false` where `#eval` gives `true`; full APPLICATION exprs evaluate
correctly. Fix: all native checks live in compiled `Walk.precheck`
(consumed via one application evalExpr); root cause open. (2) `mkApp`
applies args to leading IMPLICIT binders too — use `mkAppM` for heads
with implicit prefixes (`not_litSatI_…`, `Classical.byContradiction`).
(3) `Classical.byContradiction : (¬p → False) → p` in 4.25 core (not
`(¬p → p) → p`) — lambda body is the False proof directly. (4)
`List.mem_cons` binder order is `{α} {b} {l} {a}` (element LAST — probe
with `#check @…` before `mkAppOptM`). (5) `lemma` is a RESERVED WORD in
4.25 — `TraceBundle` literals must use the anonymous `⟨steps, lemma⟩`
form. NEXT: F4 acceptance (search → snapshot → checked theorem round
trip on the driver + factorSplit-bearing x²+2x+1 + negative probes per
R4'; the dump printer and the walk are the machinery), then F5, then
the census slice.

**F4 DONE (2026-08-09): acceptance** (build green 7610; WalkTests +2
end-to-end walks):
1. **Regeneration stability:** the `scratch_dump.lean` printer
   reproduces all 8 WalkTests snapshot defs byte-identically (mod
   whitespace). Caught en route: the printer still emitted the
   pre-4.25 `{ steps := …, lemma := … }` structure-instance form —
   fixed to the anonymous `⟨steps, lemma⟩` form (the reserved-word
   trap exactly as pinned in the F3 traps list).
2. **factorSplit drivers (fs1/fs2):** fs1 = `x0²+2x0+1 = 0 ∧ x0+1 ≠ 0`
   (repeated factor), fs2 = `x0²-3x0+2 = 0 ∧ x0-1 ≠ 0 ∧ x0-2 ≠ 0`
   (distinct factors). SURPRISE vs the F2-groundwork expectation: both
   refute at stage 0 with NO factorSplit step emitted — explain's sign
   analysis keeps the factorization internal; the arith lemmas are
   product-shaped eq-implications (`(x+1)² = 0 ⟹ x+1 = 0`; `(x-1)(x-2)
   = 0` with both factors `≠ 0`). Both walk green — discharged by F2's
   nlinarith backup path (review 5 F-ii glue: linarith first, nlinarith
   with sq_nonneg hints as backup; plain linarith is linearly
   consistent over the atoms {x², x} on these — the product step is
   load-bearing). Consequence: 19b's factorSplit identity is NOT pulled
   forward; the emission-side factorSplit steps that do occur (sq's
   `4x0² → x0·x0`) are already walked (sq pins).
3. **Negative probes:** the three WalkTests probes green (input-list
   mismatch, corrupted arith polarity, corrupted lemma); review 6 F-w
   moved payload-corruption probes to the census slice.
4. Full build green 7610 jobs; all 12c/12d pins untouched.

**12d.6b⇄19a ARC FUNCTIONALLY COMPLETE at v0.** NEXT: F5 housekeeping
(R8/R1'), then the census slice (step-fact collection + F-iv; the
√2-grade goal), then 19b/12e/14/15/16.

