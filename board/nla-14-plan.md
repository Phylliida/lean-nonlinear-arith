## nla-14 plan `boarded` (2026-08-13 eve, pre-implementation planning sweep — the `nonlinear_arith` front-end tactic)

Scope (HANDOFF + DESIGN-endgame §2.7 + board nla-14): the user-facing
`nonlinear_arith` tactic — L1 `nla_saturate` fast path, on failure
L2/L3 search→trace→checked-theorem, all inside one tactic invocation.
Owns F-y. Acceptance: user-syntax goals (ℤ and ℝ) closed end-to-end by
`by nonlinear_arith` — the sq/xl-class ℝ drivers, int1/int2-class ℤ
drivers through the 12e B&B path, and the o139 census goal — plus
layering/budget pins, full Boolean structure in hyps/goal (decision
1), and negative probes (genuine-SAT goal → clean error WITH model
display, never a wrong close). Effort estimate: 3–4 sessions (up from
2–3 — decisions 1/4 widened scope per Danielle's principles, decision
1 adding the trusted BoolForm/proxy component), meta-side-heavy with
one additive trusted-layer extension.

**What exists (recon, this session — all green, build 7612):**
- **L1 is already a tactic with the right budget shape.**
  `Tactic/Saturate.lean`: `saturateCore` (:1907) is the full L1
  pipeline (ring_nf normalize → Gröbner fast path → monomial/div-pair
  collection → fixpoint saturation → omega leaf → clause tiers);
  `withLayerHeartbeats` (:1862) is exactly the §2.7 BUDGET-SHAPE
  primitive — fresh user budget per layer, never
  fraction-of-remaining. L1 needs NO changes; the frontend calls
  `saturateCore` sandboxed and falls through on failure.
- **The walk consumes a SNAPSHOT Expr against a goal of fixed shape.**
  `Walk.walkRefutation` (Walk.lean:343): goal must be
  `∀ ρ : Nat → ℝ, (integrality hyps) → (∀ C ∈ Cs, clauseHolds ρ atoms C) → False`;
  `introToClauseHyp` (:328) already intros past non-∀ binders, so the
  12e integrality hyps (`∃ n : ℤ, ρ x = ↑n`) sit BEFORE the clause hyp
  — the convention nla-14 owns (12e decision 1; they must PRECEDE the
  clause hyp, 12e-review "considered-not-boarded" note is now a
  requirement). `precheck` (:124) pins: snapshot atoms = goal atoms,
  referenced bundle-less input clauses = goal's `Cs` in cid order.
- **The solver is PURE and callable from TacticM directly.**
  `SolverM = StateM Solver` (Solver.lean:160), `Solver.run'`
  (:174) — no IO, no unsafe at the run boundary. The driver recipe
  (scratch_dump.lean:107-121): `Solver.init` → `mkVar isInt` per var →
  `mkIneqLiteral`/`mkClause` per input clause →
  `check (Solver.resolve Explain.explain)` (Explain.lean:866) → on
  `LBool.false`, `s.refutation` holds the `SnapshotTy` value in
  INTERNAL variable order (the F2 seam, Solver.lean:1356-1362 — the
  walk's atom table is the snapshot's own array, so internal order is
  what the bridge must target; the frontend's index assignment is
  whatever it chose at `mkVar` time only up to `heuristicReorder`).
- **Quoting precedent exists but only for literals.**
  `Refute.litToExpr` (:53) + `Walk.quoteLits/quoteLitsList`
  (:178/:182). No atom/clause/step/bundle/snapshot quoting yet —
  scratch_dump's DumpPP prints paste-ready SYNTAX (the test-data
  pipeline); the tactic needs the MetaM Expr-builders instead.
- **Reification does not exist anywhere.** No Expr→MPoly/Atom
  direction in the tree (grep-clean). This is the largest new
  component.

**The three new components:**

0. **Boolean-proxy checker support (TRUSTED, additive).** `Atom`
   gains `.bool (def : BoolDef)` (proxy definitions as literal trees —
   HIERARCHICAL, post-review R-i); `interp`/`litHolds`/
   `clauseDecodable` gain
   the arm; a decide-grade Boolean reflection (`BoolForm` eval under
   `I : Nat → Prop`, kernel `taut`/`conseq` check + soundness, the
   upRefutes idiom) discharges definitional/root clause bridges.
   Search side needs NOTHING (bool vars already ported — decision 1).
1. **Reify+Tseitin+bridge (goal → refutation goal).** Parse the main
   goal's
   non-dependent prop hyps + negated goal (Verus query shape:
   context-free, only stated requires — the local context IS the
   spinoff query, no ambient mining) into: a var table (free vars of
   type ℤ → `mkVar true`, ℝ → `mkVar false`), arith atoms per
   comparison proposition, Tseitin clausification (proxy per
   non-literal subformula, `mkBoolVar` slots, definitional + root
   clauses), and per-clause bridge
   proofs `h → clauseHolds ρ atoms C`. ℤ→ℝ relaxation at the bridge:
   each ℤ comparison `a ⋈ b` becomes the ℝ sign condition on
   `↑(a−b)`'s reified poly (sound for PROVING — goal proven over ℝ
   with ℤ-atoms specializes, §2.7); per Int var the integrality hyp
   `∃ n : ℤ, ρ x = ↑n` is emitted ahead of the clause hyp. div/mod:
   hard fail at the boundary (L1-owned invariant, §2.7 — assert, don't
   silently relax). The eval-alignment of bridge proofs is by
   construction: the reifier builds the MPoly in the same term order
   `evalPoly` produces, so each bridge closes by `Iff`/defeq transport
   with at most a `ring_nf` normalization step at reify time.
2. **Quote+orchestrate (native snapshot → kernel walk).**
   `quoteAtom`/`quoteClause`/`quoteStep`/`quoteBundle`/`quoteSnapshot`
   (MetaM Expr-builders mirroring DumpPP's coverage of the grammar:
   every TraceStep arm incl. `pseudoDivision` 8-field and
   `intBranch (x, lo)`, plus the new `.bool` atom arm); run
   `Solver.run'` in TacticM; on
   `LBool.false` build the refutation goal, discharge it with the
   per-clause bridges, close the original goal by the walked
   `False`. On `LBool.true`: per-var model display — rational or
   refined dyadic interval off the RAlg/Mpbq machinery (decision 4),
   with the ℤ-relaxation caveat for integer goals. On
   `undef`/fragment exit: bounded fallthrough
   error naming the gate.

**Layering (§2.7 verbatim shape):**
```
nonlinear_arith :=
  sandboxed (withLayerHeartbeats saturateCore)   -- L1, most goals
  on failure: withLayerHeartbeats (reify → solve → quote → walk)
```
Each layer a fresh user budget; L1 failure rolls back to the original
goal before L2 sees it. L1 stays ℤ-native (omega leaf); L2 sees the
relaxed ℝ problem with integrality hyps.

**Decision points — RESOLVED (Danielle, 2026-08-13 eve, by standing
principles: 1 = match every case z3 may encounter in practice no
matter how rare; 2 = the right way even if more work; 3 = now, not
deferred; 4 = same mechanism as z3, for the same performance):**
1. **Boolean structure scope — FULL support via TSEITIN PROXIES,
   z3's mechanism** (principle 4 overturns the earlier distribution
   choice: distribution's worst-case clause explosion is a real
   PERFORMANCE divergence, and z3 clausifies with proxies precisely
   to avoid it). Three-layer finding (recon, this session):
   - **Search side: ALREADY PORTED.** z3's nlsat has native Boolean
     vars (`mk_bool_var`, nlsat_solver.cpp:464-477; `is_arith_atom(b)
     := m_atoms[b] != nullptr` :368; `m_bwatches` for unattached bool
     vars :116) and our port mirrors them — `mkBoolVar`
     (Solver.lean:183), `isArithAtom` (:245), `maxVarB : Option`
     (:256, null-for-bool = z3's null-poisoning), and the decision
     path treats non-arith bvars as pure Booleans (:486). The sq
     snapshot's `none` slot (bvar 0) was exactly a bool var.
   - **Checker side: the one real gap.** `interp`/`litHolds` map
     `none`-atom bvars to `False` and `clauseDecodable`/precheck
     reject them (Assemble.lean:63-72, :113-117; Walk.lean:167-171) —
     junk-poison, not a usable Boolean. NEW TRUSTED COMPONENT:
     extend `Atom` with a `.bool` variant carrying the proxy's
     Boolean DEFINITION as a `BoolDef` tree; `interp`/`litHolds` gain
     the arm (fuel-bounded table recursion — defs may NEST, z3's
     Tseitin shape; post-review amendment, R-i of
     board/nla-14-slice-1-design-review.md: flattening was the v1
     design and was struck for reintroducing the blowup Tseitin
     exists to avoid).
     Additive change: existing snapshots/tests elaborate untouched
     (new constructor, new match arms — NOT the SnapshotTy-shape churn
     12e decision 1-(b) was rejected over).
   - **Bridges: one decide-grade mechanism + a by-construction root.**
     Tseitin definitional clauses unfold (child proxies ABSTRACT) to
     propositional tautologies over a ≤ handful of literals —
     `taut_sound`. Root clauses: give the hyp / negated goal ITSELF a
     top-level proxy whose def is its full Boolean tree; the root
     clause is the unit `[top]` and its bridge is by-construction
     (the def tree IS the relaxed hyp; per-literal ℤ→ℝ Iffs at the
     leaves) — NO truth table ever exceeds one definitional clause
     (R-ii of the design review). `conseq_sound` stays for ad-hoc
     use. The reflection: `BoolDef.eval` under an oracle, kernel-
     computable `taut`/`conseq` + soundness, `decide` — the
     upRefutes idiom, same trust shape.
   Fidelity note: z3's VERUS path puts proxies in the outer SAT
   solver with nlsat as one-shot theory oracle; we put them INSIDE
   nlsat using its native bool-var support — z3's own standalone
   mode. Same mechanism (Tseitin + CDCL), same asymptotics; the
   arith core (the expensive part, and the fidelity-critical part)
   is byte-identical either way. No cap, no loud failure
   (principle 1).
2. **ℕ variables** — ℤ vars + an added `0 ≤ ↑n` unit clause (Verus's
   own z3 encoding; principle 2 endorses the faithful option).
3. **ℝ-typed goals** accepted directly (`mkVar false`, no integrality
   hyp) — needed anyway for the walk's own test goals to migrate to
   user syntax; cost is one arm of the var-table match.
4. **SAT-exit model display — in scope NOW** (principles 2+3; z3
   reports a model, and a bare "not provable" is the shortcut shape).
   On `LBool.true`: per-var assignment printed as rational or refined
   dyadic interval (RAlg/Mpbq machinery exists), with the ℤ-relaxation
   caveat noted for integer goals (an ℝ-model need not specialize).
   No longer delegated to nla-16.
5. **Where the tactic lives.** New module `Tactic/NonlinearArith.lean`
   (+ `NonlinearArithTests.lean`), importing Walk + Saturate; root
   `LeanNonlinearArith.lean` gains the import. No changes to existing
   modules except possibly lifting a helper or two out of Walk
   (quoteLits is already shared).

**Slice plan:**
- **Slice 0 (recon, DONE this session):** interface inventory above +
  the bool-var findings (search-side already ported, checker-side the
  gap) + decisions 1–5 resolved.
- **Slice 1 — proxy checker support (trusted, additive):**
  `Atom.bool (def : BoolDef)`; `interp`/`litHolds`/`clauseDecodable`
  arms (Assemble.lean); the `BoolDef` reflection + `taut`/`conseq`
  decide-grade check + soundness lemmas; precheck re-pin. Pins:
  definitional-clause decodability through the new arm, tautology
  discharge on the standard Tseitin clause shapes, garbage-def /
  cyclic-def poisoning, nested-proxy evaluation, existing snapshots
  untouched (the whole WalkTests/RefuteTests suite stays green
  unmodified). `DONE 2026-08-13 eve (+ same-day design review, R-i
  hierarchical-defs fix landed).`
- **Slice 2 — reify+Tseitin+bridge:** Expr→MPoly/Atom parser over the
  comparison grammar (`= ≠ < ≤ > ≥` on ℤ/ℕ/ℝ; `+ - * ^nat` literals,
  `Int.cast`/`Nat.cast` coercions); var table + `mkVar` order record;
  Tseitin clausification of BOTH the hyps and the negated goal
  (decision 1) with proxy slots via `mkBoolVar`; TOP-LEVEL PROXY per
  hyp/¬goal with unit root clauses (R-ii — by-construction bridges,
  per-literal relaxation Iffs at the leaves); integrality hyps;
  refutation-goal
  assembly via `byContradiction`. Bridge construction uses the
  `boolDefHolds` EQUATION LEMMAS (WF-compiled — no kernel defeq
  through proxies, R-i consequence). Pins: relaxed-goal shape probes
  (bridge closes; wrong-var integrality rejected — 12e's probes ported
  to user syntax), div/mod hard-fail probe, disjunctive-hyp AND
  disjunctive-goal round trips (proxies exercised both sides),
  nested-alternation stress (Tseitin linear clause count — the reason
  decision 1 exists).
- **Slice 3 — quote+orchestrate:** the five quoters (incl. the
  `.bool` atom arm); TacticM solver
  run; end-to-end `False` close on the sq/xl/int1/int2 drivers stated
  in USER syntax (no hand-written snapshot); SAT-exit model display
  (decision 4) + undef-exit error-path pins.
- **Slice 4 — tactic + acceptance:** `nonlinear_arith` elab, layering
  + per-layer budgets, L1-never-touches-L2 pin (a saturate-closable
  goal), o139 census goal in user syntax end-to-end, negative probes
  (false goal → SAT error with model, corrupted-context rejection),
  stats variant
  mirroring `nla_saturate_stats`; design review (Danielle); HANDOFF +
  memory.

**Roadmap context after nla-14 (unchanged):** nla-15 (tactus wiring,
½ session — a `require` line + closer-string emission + crate-local
check.sh gate) → nla-16 (parity harness, 1–2 + findings; owns
G8/G9/G10 + R-iii pd-driver/int1 z3-binary differential probes via
`/tmp/z3-4.12.5` + the mk_ineq_atom normalization gap + glue-
subsumption watch) = M6. Tier B (G7 rootGeneric deg ≥ 3, S1 lane
nla-10/11/30) deferred unless the harness shows the corpus needs it.
Q7 open: re-offer 11a (resultants) as the interleave lane.
