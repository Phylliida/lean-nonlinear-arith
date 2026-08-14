## nla-14 Slice 1 DESIGN REVIEW `done` (2026-08-13 eve, Danielle-requested:
divergence/regret/deferred audit of the Tseitin proxy checker support)

One REAL finding fixed same-day (R-i: flattened → hierarchical defs),
one Slice-2 design refinement (R-ii), one accepted-scope record
(R-iii), representation re-confirmed (R-iv). Build green 7612, axioms
propext/choice/Quot.sound on all touched lemmas (re-printed post-fix).

### Divergence audit (z3-4.12.5 source anchors, `git show z3-4.12.5:`)

Verified CLEAN:
- **V-1 bool-var decision polarity.** z3 `search()` decides bare bool
  vars negative-first: `decide(literal(m_bk, true))`
  (nlsat_solver.cpp:1536); the bk cursor rewinds on undo
  (`undo_bvar_assignment` :986-:998). Port: `decide ⟨b, true⟩`
  (Solver.lean:845) + `undoBvarAssignment` rewind (:482-494) — exact.
- **V-2 proxies never enter arith justifications.** z3
  `process_antecedent` (:1764): the arith lane's
  `SASSERT(is_arith_atom(b) && max_var(b) < m_xk)` (:1773) fires only
  on unassigned previous-stage literals; bool literals resolve through
  clause antecedents (`resolve_clause` :1797-1809), and
  `resolve_lazy_justification` (:1813) is explain-only (arith cores).
  Consequence for us: proxy literals can appear in learned CLAUSES
  (resolution) but never inside `.resolution (.arith core proj)`
  markers — where our `proveClauseSat` would sound-reject them anyway.
  Matches by construction.
- **V-3 `max_var` of a bool var.** z3: `null_var` (:376-379). Port:
  `maxVarB` → none (Solver.lean:256-258); the new
  `Atom.maxVar (.bool _) = none` is consistent with the search-side
  `none`-slot treatment.
- **V-4 `Atom.Holds (.bool) = False` junk arm.** Direct-consumer
  audit: Refute/Discharge operate on `IneqAtom`/`RootAtom`
  constructors explicitly or apply `ALitHolds` to constructed
  `.ineq`/`.root` atoms only — no intended flow can hit the junk arm
  silently. Table-level consumers (`interp`/`litHolds`) special-case
  `.bool` BEFORE `Atom.Holds`.
- **V-5 RUP is proxy-clean.** `upRefutes` is interpretation-agnostic;
  `litSatI_interp` re-proved across the new arm, so learned clauses
  containing proxy literals walk through the unchanged engine with
  proxy-aware interpretations.
- **V-6** Full suite green unmodified (7612); the additive-constructor
  claim held: no existing snapshot/test touched.

### Regret audit

- **R-i (REAL, FIXED same-day): flattened defs would have reintroduced
  the blowup Tseitin exists to kill.** The Slice-1 design required
  defs flattened to arith-literal leaves. Two failure modes: (a) def
  DATA grows exponentially on DAG-shared Boolean circuits (nested
  proxies inlined at each use); (b) worse — the `taut` truth tables
  are exponential in the leaves of the INLINED def, so a parent
  proxy's definitional clause inherits the child's whole subtree:
  2^|subtree| checks exactly where z3's nesting keeps everything
  local. Both are checker-side costs (search was never affected), but
  they defeat the decision-1 rationale (z3's mechanism for z3's
  performance). FIX: `BoolDef` leaves may reference proxies;
  `boolDefHolds` is fuel-bounded recursion through the atom table
  (fuel = `atoms.size + 1` at `interp`/`litHolds` — an acyclic chain
  has depth ≤ #proxies; running dry = cycle → poison `False`, the
  sound direction). Definitional-clause checks are now LOCAL (child
  proxies abstract leaves; ≤ a handful of literals each — exactly
  z3's clause-at-a-time shape). New pins: nested proxy evaluates
  through the child; cyclic defs poison.
  **Consequence for Slice 2 (load-bearing):** WF-compiled
  `boolDefHolds` has NO definitional unfolding (kernel iota blocked)
  — bridges must rewrite via the equation lemmas (simp/mkAppM on the
  auto-generated equations), never rely on raw defeq through a proxy.
  The `holds_single_*` idiom (per-shape unfolding lemmas) generalizes:
  stage proxy unfoldings as named equation-lemma rewrites.
- **R-ii (Slice-2 design refinement, no code here): root-clause
  bridges WITHOUT big truth tables.** The plan had root clauses
  discharged by `conseq` (truth table over the hyp's whole leaf set).
  Better, and z3-shaped: give the hyp / negated goal ITSELF a
  top-level proxy whose def is its full Boolean tree; the root input
  clause is the unit `[top]`; the bridge `hyp → boolDefHolds topDef`
  is by-construction (the def tree IS the relaxed hyp; only the
  per-literal ℤ→ℝ relaxation Iffs are needed at the leaves). After
  R-i + R-ii, NO truth table exceeds one definitional clause.
  `conseq` stays (proven, cheap) for probes and ad-hoc clauses.
- **R-iii (accepted scope, recorded): `ite` in arithmetic position
  maps to a FRESH OPAQUE variable.** Matches z3/Verus behavior (the
  documented if-else fragility — memory feedback
  `nonlinear_arith_ifelse`; z3 doesn't case-split these either).
  ite-LIFTING (fresh var + conditional clauses) would EXCEED z3
  fidelity — explicitly a non-goal. Any non-polynomial subterm takes
  the same opaque-variable route (z3's uninterpreted-content
  treatment).
- **R-iv (re-confirmed): `Atom.bool` constructor vs side-table.** The
  side-table alternative is the SnapshotTy/goal-shape churn rejected
  as 12e decision 1-(b); the additive constructor cost 12 mechanical
  match arms (all junk/defensive, all commented). Right call stands.

### Deferred/unboarded audit

- **D-1 → boarded into Slice 3/4:** a Tseitin'd DISJUNCTIVE driver
  (proxy in a learned clause, bool-var decision exercised) walked
  end-to-end — the plan's sq/xl/int1/int2 drivers are all conjunctive,
  so without this the proxy search path is pinned only at the
  semantics level. Plus the foreign-trace probe: proxy literal inside
  an `.arith` marker → sound rejection at `proveClauseSat`.
- **D-2 → Slice 3 note:** the SAT-model display (decision 4) skips
  proxy vars (they're frontend scaffolding, not user variables).
- **D-3 unchanged:** mk_ineq_atom normalization gap + pd-driver
  z3-binary probes (nla-16/R-iii), L1 hardening (21/22/23/07b),
  G7/S1 (Tier B). Nothing deferred-and-unboarded found.
- **Fuel-sufficiency, recorded:** acyclic proxy chains have depth ≤
  #proxy-atoms ≤ table size < fuel, so conformant tables never poison;
  only cyclic/junk defs do (sound direction), and the Slice-2 emitter
  produces acyclic-by-construction defs (proxies reference earlier
  bvars).

Slice-1 board entry + plan doc amended to strike "flattened" (the
hierarchical design is the record). HANDOFF updated.
