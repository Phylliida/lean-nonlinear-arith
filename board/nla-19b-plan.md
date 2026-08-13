## nla-19b plan `boarded` (2026-08-10, pre-implementation planning sweep — pseudoDivision → M3)

Scope (HANDOFF + G5 row): extend grammar + discharge + extraction
coverage for `pseudoDivision` steps **in the census-slice pattern**;
lift the `isV0` pseudoDivision gate (intBranch stays gated → 12e).
factorSplit identity NOT pulled forward (R6, approved). Acceptance:
census-shaped goal through search → trace → checked theorem (M3).
Effort estimate unchanged from HANDOFF: **1–2 sessions**, risk
concentrated in Slice 2 below (rebuilt-literal consumption).

**Source anchors (all `git show z3-4.12.5:`):** `simplify(literal,…)`
nlsat_explain.cpp:1096-1216 (per-replaced-factor pseudoDivision
emission; port = Explain.lean:647, verified 12d.5);
`simplify(scoped_literal_vector&, eq, max)` :1218-1265 (lc
bookkeeping + the A4/A5 assumption sites :1259-1261:
`add_lc_ineq` → LT/GT-by-lcSign literal, `add_lc_diseq` → ¬EQ literal
on the lc poly); normalize's rebuilt literal :471 (A3);
simplify-direct :1204; `select_eq` :1267-1296 (lower-stage single-
factor odd EQ atom of minimal degree in max; `min_d==1` early break);
`pseudo_remainder` polynomial.cpp:5095 (`<false,false>`: d = iteration
count, REMAINDER untopped, identity `lc(eq)^d · f = Q·eq + R` with
`deg_x R < k`; Q computed and DISCARDED at emission).

**The five simplifyLit return paths** (enumeration from the port
Explain.lean:629-686, mirrors source — this is the consumption-side
shape space):
- (a) unmodified: root-atom guard, single-factor-eq guard
  (`factors=[info.eq]`), or no factor at degree ≥ k — no new literal,
  no step emitted;
- (b) const-remainder with sign 0 → true/false literal by kind +
  `l.neg` fold, `add_lc_diseq` when non-const lc, EARLY RETURN — the
  "assumptions added are sufficient for implying the conflict"
  comment :1154-1159 is the soundness argument the discharge re-proves
  kernel-side;
- (c) rebuild below max-var ∧ `value newL = true` → KEEP ORIGINAL
  (12d.5 verified: keep-original counts as UNMODIFIED — z3 compares
  `l == new_lit`). The pseudoDivision steps STILL STAND in the bundle;
  the rewritten literal appears NOWHERE in the clause. Consumption
  must tolerate unmatched steps — participation not trust, already
  the step-fact design;
- (d) rebuild below max-var, value ≠ true → the rebuilt literal is
  emitted as an ASSUMPTION (addLiteral) and the core position replaced
  by true_literal — rebuilt literal is in the clause but NOT in the
  core projection position;
- (e) rebuild at/above max-var → `normalizeLit newL max` (A3 :
  kind-flip + neg-fold can fire AGAIN inside normalize — the double
  transformation must compose in the consumption decode).
- plus (A4/A5): at `simplifyWithEq` exit, ONE lc assumption per core
  (diseq `:1261` / ineq `:1259` by the recorded flags) — plain A-tier
  clause literals, extraction-generic.

**Slice 0 — live recon (cheap, do FIRST).** Extend
`scratch_dump.lean`'s DumpDriver with simplify-cluster drivers: core
carries a select_eq-eligible equation (single-factor odd-degree EQ
atom) AND another core literal whose factor has `degreeIn x ≥ k` (the
eq's degree in its max var). Concrete first drivers: `x0*x1 + 1 = 0 ∧
x0*x1^2 − 2 < 0`-shaped goals (eq degree 1 in x1, second factor degree
2) and a kind-flip driver (negative lc). Enumerate which of (b)/(d)/
(e) each drives; also drive the lc-ineq path (A4). Add pseudoDivision
rows to the census table. **Resolve the standing target question
here:** dump `ordering_139`'s trace and check the fragment gate —
its degree-3 cross products likely put a projection step over
`degreeIn > 2` (⇒ S1-gated rootGeneric, Tier B), in which case the
acceptance goal is the first fully-quadratic census row per HANDOFF.

**Slice 1 — grammar + trusted discharge (Trace.lean + Check.lean).**
- `Grammar.pseudoDivision` gains STRUCTURAL decide-grade conditions
  only: `lcSign ∈ {−1, 0, 1}`, the lc non-const evidence shape, and
  `r = 0 ∨ degreeIn x r < degreeIn x eq` (natively decidable — no
  polynomial arithmetic, so the `coeffsIn` kernel-reduction wall the
  HANDOFF warns about does NOT bite if we keep the grammar below it).
  The SEMANTIC content (`r` really is the pseudo-remainder, `d` the
  exponent) is NEVER grammar-trusted: discharge-time per-instance
  check below (the zeroProductClose idiom: native compute untrusted,
  ring identity kernel-closed, wrong data = loud failure).
  `grammarOK` mirror + `grammarOK_sound` case.
- Discharge identity: compute Q natively (`pseudoDivisionCore …
  quotient=true`, `partial` — native-only by construction),
  per-instance close of `∀ ρ, evalP ρ (lcPowMul) = evalP ρ Q *
  evalP ρ eq + evalP ρ r` in a sandboxed subgoal via the evalP simp
  set + `ring` (closeAlgRefl/zeroProductClose idiom; `lcPowMul` = the
  natively built `lc^d • f` — constructible via the coeffsOfValue
  reducer family, NOT kernel-pow).
- Trusted sign-transfer lemmas (Check.lean; payload-parameterized):
  from the ring identity + `evalP ρ eq = 0` + `lc ≠ 0` derive the sign
  of `evalP ρ f` by parity: **d even ⇒ sign f = sign r; d odd ⇒
  sign f = sign(lc) · sign r**, with the even-factor absorption
  (isEven ⇒ the factor's own sign is irrelevant, z3 :1133) and the
  const-remainder path-(b) collapse (`r` const-sign-0 ⇒ the factor
  vanishes ⇒ atom value by kind, :1153-1159 re-proved). Cross-check
  the source's sign-flip rule :1132-1137 line-by-line against the
  lemma statements before writing them (fidelity gate, not skim).
- A4/A5: no dedicated discharge — they are ordinary clause literals;
  the extraction must merely RECOGNIZE them as such (Slice 2).

**Slice 2 — Refute consumption (the risk item).** Extend
`collectStepFacts` with a pseudoDivision lane and `extractFacts`
rebuilt-literal normalization:
- Match clause literals against step payloads by value: a rebuilt
  literal's factor list pairs with per-step `(f, r)` payloads (the
  F2-seam by-value decode discipline; `coeffsOfValue` reducer family
  for the matching evidence — the census item-2 pattern).
- Per matched rewrite: note the ring identity (Slice 1, sandboxed
  subgoal) + `lc ≠ 0` (from the A5 diseq clause literal, or decide-
  grade when lc is const) + the sign fact on f from the sign fact on
  r — THEN the existing glue (mangle/linarith/nlinarith, findOr,
  chainLoop) consumes f-facts and r-facts uniformly.
- The A3 decode table for rebuilt literals: which (kind, neg) of the
  clause literal corresponds to which factor-list — pinned per shape
  with corruption probes in the F-w pattern (grammar-breaking vs
  grammar-clean-semantic-mismatch lanes both).
- Path (c) tolerance: unmatched pseudoDivision steps contribute
  nothing (already the participation discipline); pin with a fixture
  whose bundle carries steps for a keep-original literal.
- Fuel: rebuilt-literal path-fanout bounded per literal like the
  review-11 fix (clause-sized, never a hardcoded constant).

**Slice 3 — gate lift + acceptance.**
- `isV0`/`Walk.precheck`: drop `pseudoDivision` from the reject set;
  `intBranch` stays gated (12e). Boards-warned mitigation: pin which
  emission shapes each acceptance driver emits (the census-table
  column) BEFORE lifting, so the lift is witnessed.
- End-to-end: Slice 0's live pseudoDivision driver through search →
  trace → `nlsat_refute` checked theorem; negative probes per F-w;
  census row acceptance goal (or ordering_139, per Slice 0's finding).
- Board close-out: G5 row flips done; HANDOFF rewrite; M3 declared
  per DESIGN-endgame tiers.

**Decision points for pre-implementation design review (Danielle):**
1. Grammar tier choice (above): structural-only conditions +
   discharge-time semantic verification, vs trying to make ANY of the
   identity decide-grade. Proposal = structural-only (the partial
   `pseudoDivisionCore` never kernel-reduces; the decide-grade lane
   would need a terminating re-implementation — real work for zero
   soundness gain, since the per-instance identity check dominates).
   A terminating non-partial pseudo-division for decide-grade tickets
   is a possible R3'-grade follow-up, parked.
   **RESOLVED (Danielle, 2026-08-10): option 1.** Discussion outcome:
   the choice never touched z3 fidelity — search runs the pinned
   12d.1b-i port either way; the question was only what the trust
   overlay verifies, and the per-instance identity verifies z3's own
   mathematical contract (`lc^d·f = Q·eq + r`, deg-bound) rather than
   a second implementation's agreement with the first. Recorded
   property (strengthens the check): **d-parity is never trusted** —
   any witness (d, Q, r) of the identity with lc ≠ 0 yields the same
   sign conclusion under eq = 0 (perturbing to (d+1, lc·Q, lc·r)
   scales sign r and flips parity in cancellation); payload d/lcSign
   are pure untrusted hints. Completeness of acceptance: `ring` is
   complete for the per-instance identities, so genuine emissions
   always close. Cost model: per-(f, eq)-pair reflective close, fires
   only in simplify-cluster conflicts (select_eq-gated — zero live
   drivers emitted one across the whole 19a arc; that's why v0
   worked), heartbeat-budgeted per layer; pathological many-factor
   cores are G10 territory (nla-16 measurement; mitigation =
   bundle-level memo, no design change). Option 2 was also the
   strict-loser on cost: the wf-compiled MPoly stack can't kernel-
   compute, so it meant a SECOND polynomial representation (build +
   runtime + drift risk). nla-31's abstract termination/correctness
   proof for `pseudoDivisionCore` stands unchanged as proof-layer
   defense-in-depth — the green checker does not depend on it
   (factorM/zeroProductClose architecture exactly).
2. The standing target (ordering_139 vs first quadratic census row) is
   decided by Slice 0's dump, not in advance.
3. Path (c) keep-original semantics: confirmed by 12d.5's pin; no new
   z3 question remains.
4. Q7 lane: S1 (11a resultants ∥ 11c root continuity) stays parked
   this session — 19b is on the critical path and self-contained;
   re-offer 11a as the interleave lane once 19b lands.

**Roadmap context after 19b (unchanged from HANDOFF):** 12e (G6,
integer B&B, 1–2 sessions, mostly solver-side) → nla-14 (the
`nonlinear_arith` tactic, 2–3 sessions; owns F-y; largest remaining
piece) → nla-15 (tactus wiring, ½) → nla-16 (parity harness, 1–2 +
findings; owns G8/G9/G10 measurement) = M6. Total-to-M6 ~6–10
sessions. Tier B (G7 rootGeneric deg ≥ 3, S1 lane, 3–6 sessions, high
variance) deferred unless 16's harness shows the corpus needs it.

