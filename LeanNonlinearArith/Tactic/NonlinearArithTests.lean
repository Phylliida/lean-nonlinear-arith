import LeanNonlinearArith.Tactic.NonlinearArith

/-!
# nla-14 Slice 2 pins — the reify+Tseitin+bridge frontend

Each `nla_frontend` example reduces the goal to the refutation goal
`∀ ρ, (integrality hyps) → (∀ C ∈ Cs, clauseHolds ρ atoms C) → False`
and then closes it BY HAND — the kernel checks the full bridge chain
(dispatch, per-literal alignment chains, NNF Iffs, proxy boundaries).
-/

namespace LeanNonlinearArith.Nlsat.Tests.Frontend

open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Check

/-- sq in user syntax: `x² + y² < 0` over ℝ. The frontend's table:
slot 0 = the true-bvar, atom 1 = `x*x + y*y − 2`?? — no: `lt` on
`x*x + y*y < 0` is the difference `x*x + y*y − 0` = the sum. -/
example (x y : ℝ) (h : x * x + y * y < 0) : False := by
  nla_frontend
  intro ρ hC
  have h1 := hC [⟨1, false⟩] (by native_decide)
  simp [clauseHolds, litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt]
    at h1
  -- h1 : evalP ρ p < 0 with p the sum poly — contradict nonnegativity
  have hnn : 0 ≤ evalP ρ [(1, [(1, 2)]), (1, [(0, 2)])] := by
    simp [evalP, evalM]
    positivity
  linarith

/-- The disjunctive path: a two-literal clause from `∨` in the hyps. -/
example (x y : ℝ) (h : x * x < 0 ∨ y * y < 0) : False := by
  nla_frontend
  intro ρ hC
  have h1 := hC [⟨1, false⟩, ⟨2, false⟩] (by native_decide)
  simp [clauseHolds] at h1
  rcases h1 with h1 | h1
  · simp [litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt] at h1
    have hnn : 0 ≤ evalP ρ [(1, [(0, 2)])] := by simp [evalP, evalM]; positivity
    linarith
  · simp [litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt] at h1
    have hnn : 0 ≤ evalP ρ [(1, [(1, 2)])] := by simp [evalP, evalM]; positivity
    linarith

/-- The integrality-hyp path: an Int goal emits `∃ n : ℤ, ρ x = ↑n`
before the clause hypothesis (12e decision 1 convention). -/
example (x : ℤ) (h : x * x < 0) : False := by
  nla_frontend
  intro ρ hInt hC
  obtain ⟨n, hn⟩ := hInt
  have h1 := hC [⟨1, false⟩] (by native_decide)
  simp [clauseHolds, litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt]
    at h1
  have hnn : 0 ≤ evalP ρ [(1, [(0, 2)])] := by simp [evalP, evalM]; positivity
  linarith

/-- The proxy path: an `∧` UNDER `∨` forces a Tseitin proxy — the root
clause is `[p, sqLit]` (p = bvar 3 ⇔ x≥1 ∧ x<1 over the shared lt-atom
bvar 1; sqLit = bvar 2) and the definitional clauses re-prove the
proxy's meaning via `taut_sound`. -/
example (x : ℝ) (h : (x ≥ 1 ∧ x < 1) ∨ x * x < 0) : False := by
  nla_frontend
  intro ρ hC
  have hRoot := hC [⟨3, false⟩, ⟨2, false⟩] (by native_decide)
  simp [clauseHolds, litHolds, ALitHolds, boolDefHolds, Check.Atom.Holds,
    holds_single_lt, holds_single_gt, evalP, evalM, oddProd] at hRoot
  rcases hRoot with hLeft | hSq
  · obtain ⟨hnn, hlt⟩ := hLeft
    exact absurd hlt (not_lt.mpr hnn)
  · have hnn : 0 ≤ ρ 0 ^ 2 := sq_nonneg _
    linarith

/-- The negated-goal Not-Not path: the frontend reifies `¬¬X` to X's
clause set (a two-literal clause over the two square atoms). -/
example (x y : ℝ) : ¬ (x * x < 0 ∨ y * y < 0) := by
  nla_frontend
  intro ρ hC
  have h1 := hC [⟨1, false⟩, ⟨2, false⟩] (by native_decide)
  simp [clauseHolds] at h1
  rcases h1 with h1 | h1
  · simp [litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt] at h1
    have hnn : 0 ≤ evalP ρ [(1, [(0, 2)])] := by simp [evalP, evalM]; positivity
    linarith
  · simp [litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt] at h1
    have hnn : 0 ≤ evalP ρ [(1, [(1, 2)])] := by simp [evalP, evalM]; positivity
    linarith

/- div/mod never reach L2 (the L1-owned invariant): hard fail. The
error-surface pin: div in a hypothesis is rejected at reify. -/
/-- error: nonlinear_arith: div reaches the L2 frontend — the L1-owned invariant is broken: x / 2 -/
#guard_msgs (error) in
example (x : ℤ) (h : x / 2 * 2 = x) : False := by nla_solve

end LeanNonlinearArith.Nlsat.Tests.Frontend

/-! ## nla-14 Slice 3 pins — quote+orchestrate, NO hand-written snapshot

Each `nla_solve` example runs reify → register → solve → patch →
bridge → walk end-to-end: the solver's refutation snapshot is quoted
and kernel-checked by `Walk.walkRefutation`. -/

namespace LeanNonlinearArith.Nlsat.Tests.Orchestrate

open LeanNonlinearArith.Nlsat

/-- sq in user syntax, closed by the solver+walk (no hand-written
snapshot — the WalkTests sq pin's data pipeline replaced end-to-end). -/
example (x y : ℝ) (h : x * x + y * y < 0) : False := by
  nla_solve

/-- The disjunctive path through search: Tseitin-free two-literal
clause, CDCL resolves against the negated-goal units. -/
example (x y : ℝ) (h : x * x < 0 ∨ y * y < 0) : False := by
  nla_solve

/-- The proxy path through search: `∧` under `∨` forces a Tseitin
proxy whose definitional clauses enter the solver as inputs; the
refutation's learned clauses carry the proxy literal (D-1). -/
example (x : ℝ) (h : (x ≥ 1 ∧ x < 1) ∨ x * x < 0) : False := by
  nla_solve

/-- int1 in user syntax: the 12e branch-and-bound path (intBranch
steps, integrality hyp discharge) from a bare ℤ equation. -/
example (x : ℤ) (h : x * x = 2) : False := by
  nla_solve

/-- int2 in user syntax: two integer vars, two rounds of splits. The
trace references the x-side inputs only — the post-run Cs rebuild to
the REFERENCED inputs (precheck's contract) is load-bearing here. -/
example (x y : ℤ) (hx : x * x = 2) (hy : y * y = 3) : False := by
  nla_solve

/- Genuine-SAT goal: clean error WITH the per-var model display
(decision 4) — never a wrong close. -/
/-- error: nonlinear_arith: satisfiable — the negated goal has a model, so the goal is not provable:
  x := 1/2 -/
#guard_msgs (error) in
example (x : ℝ) (h : x ≥ 0) : x ≥ 1 := by
  nla_solve

/-- Reorder exercised end-to-end: y has the higher degree, so z3's
`reorder_lt` swaps the var order — the snapshot's atoms are in
INTERNAL order, and the captured permutation drives ρ*/integrality
assembly (Slice-3 decision A). -/
example (x y : ℝ) (h1 : x < y * y) (h2 : y * y < x - 1) : False := by
  nla_solve

/- The reorder pin at the solver seam: the captured perm is
non-identity (`perm[internal] = external`) on the same input. -/
#guard
  let prog : SolverM (Option LBool × Array Var) := do
    Solver.init
    let _ ← Solver.mkVar false  -- x (deg 1)
    let _ ← Solver.mkVar false  -- y (deg 2)
    let l1 ← Solver.mkIneqLiteral ⟨.lt, [([(1, [(0, 1)]), ((-1), [(1, 2)])], false)]⟩
    let _ ← Solver.mkClause #[l1] false
    let l2 ← Solver.mkIneqLiteral ⟨.lt, [([(1, [(1, 2)]), ((-1), [(0, 1)]), (1, [])], false)]⟩
    let _ ← Solver.mkClause #[l2] false
    Solver.checkCapturing (Solver.resolve Explain.explain)
  let ((r, perm), _) := prog.run Solver.empty
  r == some .false && perm == #[1, 0]

/- o139 in user syntax — the 6-var transitivity-of-fractions census
goal through the full pipeline (reorder live, rootGeneric/cellBound/
factorSplit steps in the walked trace). (Raised budget: reify+bridge+
walk+kernel recheck in one tactic; Slice 4's per-layer heartbeats own
the production budgeting.) -/
set_option maxHeartbeats 800000 in
example (a b c da db dc : ℝ)
    (h1 : a * db ≤ b * da) (h2 : b * dc ≤ c * db)
    (h3 : 0 < da) (h4 : 0 < db) (h5 : 0 < dc) :
    a * dc ≤ c * da := by
  nla_solve

/-! ## D-1 + foreign-`.arith`-with-proxy probe infrastructure -/

/-- The proxy driver `(x : ℝ) (h : (x ≥ 1 ∧ x < 1) ∨ x*x < 0)`,
registered exactly as the frontend does: atom 1 = `lt (x−1)`, atom 2 =
`lt (x²)`, bvar 3 = the Tseitin proxy over the shared atom. -/
private def proxyDriverRun : SolverM (Option LBool × Array Var) := do
  Solver.init
  let _ ← Solver.mkVar false
  let _ ← Solver.mkIneqAtom ⟨.lt, [([(1, [(0, 1)]), (-1, [])], false)]⟩
  let _ ← Solver.mkIneqAtom ⟨.lt, [([(1, [(0, 2)])], false)]⟩
  let _ ← Solver.mkBoolVar
  let _ ← Solver.mkClause #[⟨3, true⟩, ⟨1, true⟩] false
  let _ ← Solver.mkClause #[⟨3, true⟩, ⟨1, false⟩] false
  let _ ← Solver.mkClause #[⟨3, false⟩, ⟨1, false⟩, ⟨1, true⟩] false
  let _ ← Solver.mkClause #[⟨3, false⟩, ⟨2, false⟩] false
  Solver.checkCapturing (Solver.resolve Explain.explain)

/-- The driver's refutation snapshot (computed by the solver at compile
time — the "no hand transcription" rule), with the proxy's `.bool` def
patched into slot 3 (the orchestrate patch). -/
private def proxyDriverSnap : Walk.SnapshotTy :=
  let ((_, _), s) := proxyDriverRun.run Solver.empty
  match s.refutation with
  | some snap => (snap.1.set! 3
      (some (.bool (.and (.neg (.lit ⟨1, false⟩)) (.lit ⟨1, false⟩)))),
    snap.2.1, snap.2.2.1, snap.2.2.2)
  | none => (#[], #[], #[], {})

/- D-1 solver-side: the proxy driver's refutation LEARNS clauses over
the proxy bvar (z3's Tseitin proxies participate in CDCL search — this
is why decision 1's in-nlsat proxies are load-bearing) and the final
bundle resolves them. The nla_solve pin above walks exactly this
snapshot shape through the patched table. -/
#guard
  let ((r, _), s) := proxyDriverRun.run Solver.empty
  match s.refutation with
  | none => false
  | some (_, clauses, _, fin) =>
    r == some .false &&
    ((List.range clauses.size).filter fun cid =>
      clauses[cid]!.learned && clauses[cid]!.lits.any (·.bvar == 3)) == [5, 6] &&
    (match fin.steps.toList with
      | [.resolution (.clause 6), .resolution (.clause 5)] => true
      | _ => false)

/-- RUP-invariant poisoning: replace a `.resolution (.clause cid)`
antecedent of a proxy-carrying input clause by a FOREIGN `.arith`
marker whose clause VALUE is identical (`proj ++ core.negate` =
`clauses[cid].lits`). precheck's F-set/RUP checks are unaffected — the
rejection must come from the arith discharge. -/
private def poisonStep (clauses : Array Clause) (bundles : Array (Option TraceBundle))
    (proxy : Nat) : TraceStep → Option TraceStep
  | .resolution (.clause cid) =>
    if cid < bundles.size && bundles[cid]!.isNone &&
        clauses[cid]!.lits.any (·.bvar == proxy) then
      some (.resolution (.arith (clauses[cid]!.lits.map Literal.negate) #[]))
    else none
  | _ => none

/-- Poison the first poisonable step of a bundle, if any. -/
private def poisonBundle (clauses : Array Clause) (bundles : Array (Option TraceBundle))
    (proxy : Nat) (b : TraceBundle) : Option TraceBundle := Id.run do
  let mut steps : List TraceStep := []
  let mut found := false
  for st in b.steps.toList do
    if !found then
      match poisonStep clauses bundles proxy st with
      | some st' => steps := st' :: steps; found := true
      | none => steps := st :: steps
    else
      steps := st :: steps
  if found then return some { b with steps := steps.reverse.toArray }
  else return none

/-- The poisoned snapshot: first proxy-carrying input-clause antecedent
(learned bundles in cid order, then the final bundle) replaced by the
foreign `.arith` marker. -/
private def corruptSnap : Walk.SnapshotTy := Id.run do
  let (atoms, clauses, bundles, fin) := proxyDriverSnap
  let mut bundles := bundles
  let mut fin := fin
  let mut done := false
  for i in [:bundles.size] do
    if !done then
      if let some b := bundles[i]! then
        if let some b' := poisonBundle clauses bundles 3 b then
          bundles := bundles.set! i b'
          done := true
  if !done then
    match poisonBundle clauses bundles 3 fin with
    | some f' => fin := f'
    | none => pure ()
  return (atoms, clauses, bundles, fin)

/-- The corrupt snapshot's referenced inputs (the goal's `Cs` must equal
these — the walk's input-clause contract). -/
private def corruptCs : List (List Literal) :=
  (Walk.referencedInputCids corruptSnap.2.2.1
    corruptSnap.2.2.2).toList.map fun cid => corruptSnap.2.1[cid]!.lits.toList

/- Foreign `.arith`-with-proxy: sound rejection. The poisoned `.arith`
marker mentions the proxy literal; `extractFacts` has no `.bool` lane,
so the proxy is skipped, the arith glue fails, and the walk rejects —
never an unsound accept. -/
/-- error: nlsat_refute: arith lemma [{ bvar := 3, neg := false },
 { bvar := 2, neg := false }] failed to discharge: Application type mismatch: The argument
  h_i
has type
  litSatI (interp ρ corruptSnap.1) { bvar := 2, neg := false } → False
but is expected to have type
  ¬Check.IneqAtom.Holds ρ { kind := IneqKind.lt, factors := [([(1, [(0, 2)])], false)] }
in the application
  mt (Check.holds_single_lt ρ [(1, [(0, 2)])]).mpr h_i -/
#guard_msgs (error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ corruptCs, clauseHolds ρ corruptSnap.1 C) → False := by
  nlsat_refute corruptSnap

/- undef exit at the solver seam: conflict budget exhausted
(`maxConflicts := 0`, so the first resolved conflict trips the z3
budget check, Solver.lean:835) — the orchestrate catch-all reports
this as the bounded-exit error, never a wrong close. -/
#guard
  let ((r, _), _) := proxyDriverRun.run { Solver.empty with maxConflicts := 0 }
  r == some .undef

/-! ## Slice-3 review R-ii/R-iii — bridge-arm + interaction coverage

The kernel caught the `.le/.ge,false` double-negation precisely because
no Slice-2 pin had a ≤/≥ GOAL. These pins close the (ck, polarity)
matrix — every `mkLitIff` arm now has an end-to-end driver — plus the
reifyProp Iff/ite shapes and the decision-2 ℕ path. All tiny/linear;
the bridge is built before the (trivial) search either way. -/

/-- `.lt,true` arm (negated lt literal — a `<` goal disproved). -/
example (x : ℝ) (h : x ≤ 0) : x < 1 := by nla_solve

/-- `.gt,true` arm (a `>` goal disproved). -/
example (x : ℝ) (h : x ≥ 2) : x > 1 := by nla_solve

/-- `.eq,true` (goal) + `.eq,false` (hyp) arms in one driver. -/
example (x : ℝ) (h : x = 2) : x = 2 := by nla_solve

/-- `.ge,false` arm (a `≥` goal disproved — the fixed code path;
o139 pins `.le,false`). -/
example (x : ℝ) (h : x ≥ 2) : x ≥ 1 := by nla_solve

/-- `.ne,true` arm (a ≠ hyp, positive polarity). -/
example (x : ℝ) (h1 : x ≠ 0) (h2 : x * x ≤ 0) : False := by nla_solve

/-- `.ne,false` arm (a ≠ goal — the `not_not` chain). -/
example (x : ℝ) (h : x * x < 0) : x ≠ 0 := by nla_solve

/-- Iff hyp through the frontend (iff_cnf + proxies under the and). -/
example (x : ℝ) (h : x ≥ 1 ↔ x ≥ 2) (h1 : x ≥ 1) (h2 : x < 2) : False := by
  nla_solve

/-- ite-in-prop-position hyp (ite_cnf). -/
example (x : ℝ) (h : if x ≥ 1 then x ≥ 2 else x ≤ 0) (h1 : x ≥ 1) (h2 : x < 2) :
    False := by
  nla_solve

/-- The decision-2 ℕ path: cast links, the `0 ≤ ↑n` root clause, the
ℕ integrality witness, and B&B over a nat var. -/
example (n : ℕ) (h : n * n = 2) : False := by nla_solve

/-- R-iii: intBranch × non-identity reorder — y registers first (deg 1),
x second (deg 2), so `reorder_lt` swaps them (perm = #[1, 0]) and the
B&B split on x lands on an INTERNAL index whose integrality hyp was
emitted via the captured perm. -/
example (y x : ℤ) (h1 : y < x) (h2 : x * x = 2) : False := by nla_solve

end LeanNonlinearArith.Nlsat.Tests.Orchestrate

/-! ## nla-14 Slice 4 pins — the layered `nonlinear_arith` tactic

L1 = sandboxed `saturateCore` fast path; L2 = the Slice-3 orchestrate
pipeline. Layer assignments are PROBE-VERIFIED (scratch_layerprobe.lean,
2026-08-14): int1/int2 close in L1 (the mined `x*x = 2` down-propagates
to |x| ≤ 1 and the corner rules refute — no B&B needed), so the
B&B-through-layering coverage is carried by the `x*(x+1) = 3` drivers
(L1 cannot bound x from the equation alone: `x*x = 3−x` gives only the
one-sided x ≤ 3). The `nlaL2Runs` counter (bumped inside `orchestrate`)
is the layer-pin mechanism; `run_cmd` sandwiches read it. -/

namespace LeanNonlinearArith.Nlsat.Tests.NonlinearArith

open LeanNonlinearArith.Nlsat.Frontend (nlaL2Runs nlaL2Conflicts)

/- L1-never-touches-L2 (THE Slice-4 layering pin): a saturate-closable
ℤ goal must close without entering the solver. -/
run_cmd nlaL2Runs.set 0
example (x : ℤ) : 0 ≤ x * x := by nonlinear_arith
run_cmd do unless (← nlaL2Runs.get) == 0 do
  throwError "L2 ran on an L1-closable goal"

/- L1, second shape: the tangent-plane specimen (corner rules + mined
anchors); the optional round numeral is exercised here. -/
run_cmd nlaL2Runs.set 0
example (x y : ℤ) (h1 : 1 ≤ x) (h2 : 1 ≤ y) : x + y ≤ x * y + 1 := by
  nonlinear_arith 5
run_cmd do unless (← nlaL2Runs.get) == 0 do
  throwError "L2 ran on the tangent specimen"

/- PROBE FINDING: int1 closes in L1 — no B&B needed. The 12e integer
path stays pinned at the nla_solve seam (Tests.Orchestrate) and by the
B&B drivers below. -/
run_cmd nlaL2Runs.set 0
example (x : ℤ) (h : x * x = 2) : False := by nonlinear_arith
run_cmd do unless (← nlaL2Runs.get) == 0 do
  throwError "int1 fell through to L2"

/- L2 acceptance: sq over ℝ (L1's omega leaf is ℤ-native; ℝ goals fall
through by design, §2.7). -/
run_cmd nlaL2Runs.set 0
example (x y : ℝ) (h : x * x + y * y < 0) : False := by nonlinear_arith
run_cmd do unless (← nlaL2Runs.get) == 1 do
  throwError "sq did not take the L2 path"

/- The same sq driver through `nonlinear_arith_stats`: L1 throws before
its stats print, so the closing-layer line is the ONLY info message —
pinned byte-for-byte, conflict count included (deterministic solver). -/
/-- info: nonlinear_arith: L1 failed to close the goal; closed by L2 (nlsat search → trace → kernel-checked walk, 4 conflicts) -/
#guard_msgs (info) in
example (x y : ℝ) (h : x * x + y * y < 0) : False := by nonlinear_arith_stats

/- The rest of the Slice-3 driver set through the layered entry
(acceptance sweep): disj, proxy, int2 (L1 refutes it from one square
equation alone — the unused-hyp linter is suppressed, the second
equation is the int2 SHAPE), the ℝ reorder driver, and the decision-2
ℕ path (L2 — L1 does not mine the ℕ casts). -/
example (x y : ℝ) (h : x * x < 0 ∨ y * y < 0) : False := by nonlinear_arith
example (x : ℝ) (h : (x ≥ 1 ∧ x < 1) ∨ x * x < 0) : False := by nonlinear_arith
set_option linter.unusedVariables false in
example (x y : ℤ) (hx : x * x = 2) (hy : y * y = 3) : False := by nonlinear_arith
example (x y : ℝ) (h1 : x < y * y) (h2 : y * y < x - 1) : False := by nonlinear_arith
example (n : ℕ) (h : n * n = 2) : False := by nonlinear_arith

/- B&B through the layering: `x*(x+1) = 3` has the real root
(−1+√13)/2 but no integer one; L1 cannot bound x from the equation
alone, so this falls to L2 and the 12e intBranch splits refute it.
Carries the int1/int2-class-through-B&B acceptance for the layered
tactic. -/
run_cmd nlaL2Runs.set 0
example (x : ℤ) (h : x * (x + 1) = 3) : False := by nonlinear_arith
run_cmd do unless (← nlaL2Runs.get) == 1 do
  throwError "the B&B driver did not take the L2 path"

/- … × non-identity reorder (the R-iii interaction through the
layering): h1 registers y first (deg 1 — it exists for the registration
order, hence the suppressed lint), x second (deg 2), so `reorder_lt`
swaps (perm = #[1,0]) and the intBranch split on x discharges against
the integrality hyp at the INTERNAL index. -/
run_cmd nlaL2Runs.set 0
set_option linter.unusedVariables false in
example (y x : ℤ) (h1 : y < x) (h2 : x * (x + 1) = 3) : False := by
  nonlinear_arith
run_cmd do unless (← nlaL2Runs.get) == 1 do
  throwError "the B&B×reorder driver did not take the L2 path"

/- o139 census goal, user syntax, end-to-end through the layering: L1
fails (degree-3 cross products are nlsat-tier) and rolls back clean;
L2 walks the 6-conflict refutation. The budget lives ON THE TEST —
each layer gets the fresh user maxHeartbeats (Slice 4 owns budgeting). -/
run_cmd nlaL2Runs.set 0
set_option maxHeartbeats 800000 in
example (a b c da db dc : ℝ)
    (h1 : a * db ≤ b * da) (h2 : b * dc ≤ c * db)
    (h3 : 0 < da) (h4 : 0 < db) (h5 : 0 < dc) :
    a * dc ≤ c * da := by
  nonlinear_arith
run_cmd do unless (← nlaL2Runs.get) == 1 do
  throwError "o139 did not take the L2 path"

/- The prelude's True short-circuit survives the layering (L1 cannot
work on `True`; L2's prelude assigns `True.intro` before any solver
work — Slice-4 review R-i: the entry-hook semantics are counter-pinned
here, L2 entered exactly once with zero solver conflicts). -/
run_cmd nlaL2Runs.set 0
example : True := by nonlinear_arith
run_cmd do unless (← nlaL2Runs.get) == 1 && (← nlaL2Conflicts.get) == 0 do
  throwError "the True goal did not take the L2 prelude short-circuit"

/- R-i: the stats line names what actually happened — the prelude
variant, byte-exact (no fabricated conflict count). -/
/-- info: nonlinear_arith: L1 failed to close the goal; closed by L2's prelude (True goal — no solver work) -/
#guard_msgs (info) in
example : True := by nonlinear_arith_stats

/- Genuine-SAT through the layering: L1 fails, the rollback wipes its
messages, and L2's model display is the ONLY error — byte-identical to
the nla_solve pin (decision 4; never a wrong close). -/
/-- error: nonlinear_arith: satisfiable — the negated goal has a model, so the goal is not provable:
  x := 1/2 -/
#guard_msgs (error) in
example (x : ℝ) (h : x ≥ 0) : x ≥ 1 := by nonlinear_arith

/- div/mod through the layering: L1 owns div/mod but this goal is
unprovable (x = 0 satisfies the hyp), so L1 fails and L2's reify
boundary hard-fails — byte-identical to the nla_solve surface. -/
/-- error: nonlinear_arith: div reaches the L2 frontend — the L1-owned invariant is broken: x / 2 -/
#guard_msgs (error) in
example (x : ℤ) (h : x / 2 * 2 = x) : False := by nonlinear_arith

/- Corrupted-context rejection: a hypothesis outside the reify grammar
(an existential) is a loud error, never a silent drop. -/
/-- error: nonlinear_arith: unsupported hypothesis shape: ∃ y, x < y -/
#guard_msgs (error) in
example (x : ℝ) (h : ∃ y : ℝ, x < y) : x * x < 0 := by nonlinear_arith

end LeanNonlinearArith.Nlsat.Tests.NonlinearArith
