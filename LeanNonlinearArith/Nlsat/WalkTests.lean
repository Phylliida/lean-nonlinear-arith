import LeanNonlinearArith.Nlsat.Walk

/-!
# nla-19a F3 tests — the DAG walk end-to-end on live refutations

Snapshot data reproduced through the F2 seam (`Solver.run'` +
`check (resolve Explain.explain)`, printed programmatically — no hand
transcription): the 2-var acceptance driver
`x0²+x1² ≥ 2 ∧ x0 ≤ 1 ∧ x1 < 1 ∧ x0 > 0 ∧ x1 > 0` (2 learned bundles +
final) and the x0²+x1² < 0 refutation (3 learned bundles + final).
-/

namespace LeanNonlinearArith.Nlsat.Tests.Walk

open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Check

/-! ## The x0²+x1² < 0 refutation (sq) -/

private def sqAtoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.lt, [([(1, [(1, 2)]), (1, [(0, 2)])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩)]

private def sqClauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩], learned := true, deleted := false },
   { lits := #[⟨3, false⟩], learned := true, deleted := false },
   { lits := #[⟨4, false⟩], learned := true, deleted := false }]

private def sqBundles : Array (Option TraceBundle) :=
  #[none,
   none,
   some ⟨#[.resolution (.clause 1),
      .factorSplit [(4, [(0, 2)])] #[[(1, [(0, 1)])]] #[[(1, [(0, 1)])]],
      .resolution (.arith #[⟨1, false⟩] #[⟨2, true⟩])], #[⟨2, true⟩]⟩,
   some ⟨#[.resolution (.clause 1),
      .factorSplit [(4, [(0, 2)])] #[[(1, [(0, 1)])]] #[],
      .linearRoot .le 0 [(1, [(0, 1)])] false none,
      .cellBound .upper .le 0 1 [(1, [(0, 1)])],
      .resolution (.arith #[⟨1, false⟩] #[⟨3, false⟩])], #[⟨3, false⟩]⟩,
   some ⟨#[.resolution (.clause 1),
      .factorSplit [(4, [(0, 2)])] #[[(1, [(0, 1)])]] #[],
      .linearRoot .ge 0 [(1, [(0, 1)])] false none,
      .cellBound .lower .ge 0 1 [(1, [(0, 1)])],
      .resolution (.arith #[⟨1, false⟩] #[⟨4, false⟩])], #[⟨4, false⟩]⟩]

private def sqFinal : TraceBundle :=
  ⟨#[.resolution (.clause 4),
      .leafNumeric 0,
      .resolution (.arith #[⟨3, false⟩, ⟨4, false⟩] #[]),
      .resolution (.clause 3)], #[]⟩

/-- End-to-end: the sq refutation walked from the single input clause
`x0²+x1² < 0`. -/
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩]], clauseHolds ρ sqAtoms C) → False := by
  nlsat_refute ⟨sqAtoms, sqClauses, sqBundles, sqFinal⟩

/-! ## The 2-var acceptance driver (drv) -/

private def drvAtoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.lt, [([(1, [(1, 2)]), (1, [(0, 2)]), ((-2), [])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(1, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(1, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)]), (1, [])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 2)]), ((-2), [])], false)]⟩)]

private def drvClauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, true⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩], learned := false, deleted := false },
   { lits := #[⟨3, false⟩], learned := false, deleted := false },
   { lits := #[⟨4, false⟩], learned := false, deleted := false },
   { lits := #[⟨5, false⟩], learned := false, deleted := false },
   { lits := #[⟨6, true⟩, ⟨7, true⟩], learned := true, deleted := false },
   { lits := #[⟨4, true⟩, ⟨8, true⟩, ⟨9, true⟩], learned := true, deleted := false }]

private def drvBundles : Array (Option TraceBundle) :=
  #[none,
   none,
   none,
   none,
   none,
   none,
   some ⟨#[.resolution (.clause 1),
      .factorSplit [(4, [(0, 2)]), ((-8), [])] #[[(1, [(0, 2)]), ((-2), [])]] #[],
      .factorSplit [(1, [(0, 2)]), ((-2), [])] #[[(1, [(0, 2)]), ((-2), [])]] #[],
      .factorSplit [(1, [(0, 2)]), ((-1), [])] #[[(1, [(0, 1)]), (1, [])], [(1, [(0, 1)]), ((-1), [])]] #[],
      .linearRoot .gt 0 [(1, [(0, 1)]), (1, [])] false none,
      .cellBound .lower .gt 0 1 [(1, [(0, 1)]), (1, [])],
      .linearRoot .lt 0 [(1, [(0, 1)]), ((-1), [])] false none,
      .cellBound .upper .lt 0 1 [(1, [(0, 1)]), ((-1), [])],
      .resolution (.arith #[⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩] #[⟨6, true⟩, ⟨7, true⟩]),
      .resolution (.clause 5),
      .resolution (.clause 3)], #[⟨6, true⟩, ⟨7, true⟩]⟩,
   some ⟨#[.resolution (.clause 1),
      .factorSplit [(4, [(0, 2)]), ((-8), [])] #[[(1, [(0, 2)]), ((-2), [])]] #[],
      .factorSplit [(1, [(0, 2)]), ((-2), [])] #[[(1, [(0, 2)]), ((-2), [])]] #[],
      .factorSplit [(1, [(0, 2)]), ((-1), [])] #[[(1, [(0, 1)]), (1, [])], [(1, [(0, 1)]), ((-1), [])]] #[[(1, [(0, 1)]), ((-1), [])]],
      .thomQuadratic .gt 0 1 [(1, [(0, 2)]), ((-2), [])] 1 1 1 (-1),
      .cellBound .lower .gt 0 1 [(1, [(0, 2)]), ((-2), [])],
      .thomQuadratic .lt 0 2 [(1, [(0, 2)]), ((-2), [])] 1 1 1 (-1),
      .cellBound .upper .lt 0 2 [(1, [(0, 2)]), ((-2), [])],
      .resolution (.arith #[⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩] #[⟨8, true⟩, ⟨4, true⟩, ⟨9, true⟩]),
      .resolution (.clause 5),
      .resolution (.clause 3)], #[⟨4, true⟩, ⟨8, true⟩, ⟨9, true⟩]⟩]

private def drvFinal : TraceBundle :=
  ⟨#[.resolution (.clause 7),
      .leafNumeric 0,
      .resolution (.arith #[⟨7, true⟩, ⟨9, true⟩, ⟨2, true⟩] #[]),
      .leafNumeric 0,
      .resolution (.arith #[⟨7, true⟩, ⟨8, true⟩, ⟨2, true⟩] #[]),
      .resolution (.clause 6),
      .leafNumeric 0,
      .resolution (.arith #[⟨4, false⟩, ⟨6, true⟩] #[]),
      .resolution (.clause 4),
      .resolution (.clause 2)], #[]⟩

/-- End-to-end: the acceptance driver refutation walked from the five
input clauses. -/
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, true⟩], [⟨2, true⟩], [⟨3, false⟩], [⟨4, false⟩], [⟨5, false⟩]],
      clauseHolds ρ drvAtoms C) → False := by
  nlsat_refute ⟨drvAtoms, drvClauses, drvBundles, drvFinal⟩

/-! ## Negative probes -/

/- Input-list mismatch (clause 5 dropped): the walk computes the
referenced input clauses from the snapshot and must reject. -/
#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, true⟩], [⟨2, true⟩], [⟨3, false⟩], [⟨4, false⟩]],
      clauseHolds ρ drvAtoms C) → False := by
  nlsat_refute ⟨drvAtoms, drvClauses, drvBundles, drvFinal⟩

/- Corrupted arith marker: bundle 6's proj first literal polarity
flipped (`⟨6, false⟩` for `⟨6, true⟩`) — the arith lemma is invalid
(RefuteTests negative probe) and the walk must reject. -/
private def drvBundlesBadArith : Array (Option TraceBundle) :=
  drvBundles.set! 6 (some ⟨#[.resolution (.clause 1),
      .factorSplit [(4, [(0, 2)]), ((-8), [])] #[[(1, [(0, 2)]), ((-2), [])]] #[],
      .factorSplit [(1, [(0, 2)]), ((-2), [])] #[[(1, [(0, 2)]), ((-2), [])]] #[],
      .factorSplit [(1, [(0, 2)]), ((-1), [])] #[[(1, [(0, 1)]), (1, [])], [(1, [(0, 1)]), ((-1), [])]] #[],
      .linearRoot .gt 0 [(1, [(0, 1)]), (1, [])] false none,
      .cellBound .lower .gt 0 1 [(1, [(0, 1)]), (1, [])],
      .linearRoot .lt 0 [(1, [(0, 1)]), ((-1), [])] false none,
      .cellBound .upper .lt 0 1 [(1, [(0, 1)]), ((-1), [])],
      .resolution (.arith #[⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩] #[⟨6, false⟩, ⟨7, true⟩]),
      .resolution (.clause 5),
      .resolution (.clause 3)], #[⟨6, true⟩, ⟨7, true⟩]⟩)

#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, true⟩], [⟨2, true⟩], [⟨3, false⟩], [⟨4, false⟩], [⟨5, false⟩]],
      clauseHolds ρ drvAtoms C) → False := by
  nlsat_refute ⟨drvAtoms, drvClauses, drvBundlesBadArith, drvFinal⟩

/- Corrupted learned clause: clause 6 and bundle 6's lemma both shrunk
to `[⟨6, true⟩]` (V1 stays consistent) — the RUP check cannot derive it
from the antecedents and the walk must reject. -/
private def drvClausesBadRup : Array Clause :=
  drvClauses.set! 6 { lits := #[⟨6, true⟩], learned := true, deleted := false }

private def drvBundlesBadRup : Array (Option TraceBundle) :=
  drvBundles.set! 6 (some ⟨#[.resolution (.clause 1),
      .factorSplit [(4, [(0, 2)]), ((-8), [])] #[[(1, [(0, 2)]), ((-2), [])]] #[],
      .factorSplit [(1, [(0, 2)]), ((-2), [])] #[[(1, [(0, 2)]), ((-2), [])]] #[],
      .factorSplit [(1, [(0, 2)]), ((-1), [])] #[[(1, [(0, 1)]), (1, [])], [(1, [(0, 1)]), ((-1), [])]] #[],
      .linearRoot .gt 0 [(1, [(0, 1)]), (1, [])] false none,
      .cellBound .lower .gt 0 1 [(1, [(0, 1)]), (1, [])],
      .linearRoot .lt 0 [(1, [(0, 1)]), ((-1), [])] false none,
      .cellBound .upper .lt 0 1 [(1, [(0, 1)]), ((-1), [])],
      .resolution (.arith #[⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩] #[⟨6, true⟩, ⟨7, true⟩]),
      .resolution (.clause 5),
      .resolution (.clause 3)], #[⟨6, true⟩]⟩)

#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, true⟩], [⟨2, true⟩], [⟨3, false⟩], [⟨4, false⟩], [⟨5, false⟩]],
      clauseHolds ρ drvAtoms C) → False := by
  nlsat_refute ⟨drvAtoms, drvClausesBadRup, drvBundlesBadRup, drvFinal⟩

end LeanNonlinearArith.Nlsat.Tests.Walk
