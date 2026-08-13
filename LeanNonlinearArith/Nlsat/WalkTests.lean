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

/-! ## factorSplit drivers (fs1: repeated factor, fs2: distinct factors) -/

/-- `x0²+2x0+1 = 0 ∧ x0+1 ≠ 0` — eq-implication through the repeated
factor (x0+1)²; the solver refutes at stage 0 with a single arith
lemma (no factorSplit step emitted — the factorization is internal to
explain's sign analysis). -/
private def fs1Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(0, 2)]), (2, [(0, 1)]), (1, [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)]), (1, [])], false)]⟩)]

private def fs1Clauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩], learned := false, deleted := false }]

private def fs1Bundles : Array (Option TraceBundle) :=
  #[none,
   none,
   none]

private def fs1Final : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .leafNumeric 0,
      .resolution (.arith #[⟨1, false⟩, ⟨2, true⟩] #[]),
      .resolution (.clause 2)], #[]⟩

example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, true⟩]], clauseHolds ρ fs1Atoms C) → False := by
  nlsat_refute ⟨fs1Atoms, fs1Clauses, fs1Bundles, fs1Final⟩

/-- `x0²-3x0+2 = 0 ∧ x0-1 ≠ 0 ∧ x0-2 ≠ 0` — the zero-product split over
two distinct factors (x0-1)(x0-2). -/
private def fs2Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(0, 2)]), ((-3), [(0, 1)]), (2, [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)]), ((-2), [])], false)]⟩)]

private def fs2Clauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩], learned := false, deleted := false },
   { lits := #[⟨3, true⟩], learned := false, deleted := false }]

private def fs2Bundles : Array (Option TraceBundle) :=
  #[none,
   none,
   none,
   none]

private def fs2Final : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .leafNumeric 0,
      .resolution (.arith #[⟨1, false⟩, ⟨2, true⟩, ⟨3, true⟩] #[]),
      .resolution (.clause 3),
      .resolution (.clause 2)], #[]⟩

example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, true⟩], [⟨3, true⟩]], clauseHolds ρ fs2Atoms C) → False := by
  nlsat_refute ⟨fs2Atoms, fs2Clauses, fs2Bundles, fs2Final⟩

/-! ## Zero-product walks (design review 7 F-v; closed by the G1
`zeroProductClose` discharge in Refute.lean — native factorization +
kernel-verified product identity + `mul_ne_zero` chain). -/

/-- `(x0-1)(x0-2)(x0-3) = 0` with all three factors `≠ 0`. -/
private def fs3Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(0, 3)]), ((-6), [(0, 2)]), (11, [(0, 1)]), ((-6), [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)]), ((-2), [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)]), ((-3), [])], false)]⟩)]

private def fs3Clauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩], learned := false, deleted := false },
   { lits := #[⟨3, true⟩], learned := false, deleted := false },
   { lits := #[⟨4, true⟩], learned := false, deleted := false }]

private def fs3Bundles : Array (Option TraceBundle) := #[none, none, none, none, none]

private def fs3Final : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .leafNumeric 0,
      .resolution (.arith #[⟨1, false⟩, ⟨2, true⟩, ⟨3, true⟩, ⟨4, true⟩] #[]),
      .resolution (.clause 4),
      .resolution (.clause 3),
      .resolution (.clause 2)], #[]⟩

example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, true⟩], [⟨3, true⟩], [⟨4, true⟩]],
      clauseHolds ρ fs3Atoms C) → False := by
  nlsat_refute ⟨fs3Atoms, fs3Clauses, fs3Bundles, fs3Final⟩

/- Corrupted fs3: the final arith core drops `⟨4, true⟩` (the x0-3 ≠ 0
conjunct). The resulting clause `p ≠ 0 ∨ x0-1 = 0 ∨ x0-2 = 0` is
INVALID (falsified at x0 = 3) — but the RUP chain still closes
propositionally, so ONLY the arith discharge can reject it: the
zero-product gate finds factor x0-3 unmatched and falls through to the
glue, which fails. A soundness probe of the G1 gate + glue layering. -/
private def fs3FinalBad : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .leafNumeric 0,
      .resolution (.arith #[⟨1, false⟩, ⟨2, true⟩, ⟨3, true⟩] #[]),
      .resolution (.clause 3),
      .resolution (.clause 2)], #[]⟩

#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, true⟩], [⟨3, true⟩]],
      clauseHolds ρ fs3Atoms C) → False := by
  nlsat_refute ⟨fs3Atoms, fs3Clauses, fs3Bundles, fs3FinalBad⟩

/-- `(x0+1)³ = 0 ∧ x0+1 ≠ 0` — a single REPEATED factor at
multiplicity 3 (the `pow_ne_zero` leg of the zero-product close). -/
private def fs4Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(0, 3)]), (3, [(0, 2)]), (3, [(0, 1)]), (1, [])], false)]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1)]), (1, [])], false)]⟩)]

private def fs4Clauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩], learned := false, deleted := false }]

private def fs4Bundles : Array (Option TraceBundle) := #[none, none, none]

private def fs4Final : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .leafNumeric 0,
      .resolution (.arith #[⟨1, false⟩, ⟨2, true⟩] #[]),
      .resolution (.clause 2)], #[]⟩

example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, true⟩]], clauseHolds ρ fs4Atoms C) → False := by
  nlsat_refute ⟨fs4Atoms, fs4Clauses, fs4Bundles, fs4Final⟩

/-! ## R2' (review 14) — duplicate-literal propagation stall + hardening -/

/-- Pre-dedup (the R2' stall): EVERY clause carries duplicate literals;
`clauseStatus` reads `[l, l]`-unassigned as `.other` (not unit), so no
unit ever forms, propagation never starts, and the refutation check
fails even though `{l, ¬l}` is unsatisfiable. -/
example : upRefutes [[⟨0, false⟩, ⟨0, false⟩], [⟨0, true⟩, ⟨0, true⟩]] []
    = false := by decide

/-- Post-dedup (the hardening, review 14): the duplicated clauses are
unit, `{l, ¬l}` refutes. This is the computation the walk's decide
site now runs (FE/targetE dedup'd before `upRefutes`). -/
example : upRefutes
    ([[⟨0, false⟩, ⟨0, false⟩], [⟨0, true⟩, ⟨0, true⟩]].map (·.dedup)) []
    = true := by decide

/-- A partial case: only the driver clause is duplicated. Pre-dedup
the singleton `¬l` still drives, so this one refutes either way —
the stall needs EVERY clause duplicated (registered for the record). -/
example : upRefutes [[⟨0, true⟩], [⟨0, false⟩, ⟨0, false⟩]] [] = true := by
  decide

/-! ## The √2-grade acceptance goal (census slice G4)

`x0 ≥ 0 ∧ x0² ≥ 2 ∧ x0 ≤ 1` — the census slice's standing acceptance
goal. LANDED as a stage-0, literal-local refutation (the solver's
core is the three input atoms themselves; the arith lemma needs no
cellBound — census result, 2026-08-10). Snapshot data machine-generated
by `scratch_dump.lean` (paste-ready printer output, no hand
transcription). -/

private def sqrt2Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.lt, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 2)]), ((-2), [])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)]), ((-1), [])], false)]⟩)]

private def sqrt2Clauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, true⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩], learned := false, deleted := false },
   { lits := #[⟨3, true⟩], learned := false, deleted := false }]

private def sqrt2Bundles : Array (Option TraceBundle) :=
  #[none,
   none,
   none,
   none]

private def sqrt2Final : TraceBundle :=
  ⟨#[.resolution (.clause 2),
      .leafNumeric 0,
      .resolution (.arith #[⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩] #[]),
      .resolution (.clause 3),
      .resolution (.clause 1)], #[]⟩

/-- End-to-end: the √2-grade refutation walked from the three input
clauses (referenced in cid order 1, 2, 3). -/
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, true⟩], [⟨2, true⟩], [⟨3, true⟩]],
      clauseHolds ρ sqrt2Atoms C) → False := by
  nlsat_refute ⟨sqrt2Atoms, sqrt2Clauses, sqrt2Bundles, sqrt2Final⟩

/-! ## G4 census slice — rootGeneric-definite-disc (synthetic fixture)

`rootGeneric` at deg ≤ 2 is unreachable via z3-4.12.5 production reads
(the generic fallback of `add_root_literal` needs `mk_quadratic_root`
to fail, but a deg-≤2 poly with an isolated root always has `sq ≥ 0`;
negative-disc quads have no roots and never reference one), so this
family gets SYNTHETIC pins — the foreign-trace defensive grammar
region (fs3FinalBad discipline; hand-written snapshot, not
machine-generated). The clause `¬(x0 = root₁(x0²+1))`: the atom's
`i = 1 ≤ rootCount = 0` (disc = −4) is false at every ρ, so the
single-literal arith lemma is valid; the extraction's `.rootPair`
fact + `rootDefiniteClose`'s neg-disc lane discharge it. -/

private def rgAtoms : Array (Option Atom) :=
  #[none,
   some (.root ⟨.eq, 0, 1, [(1, [(0, 2)]), (1, [])]⟩)]

private def rgClauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false }]

private def rgBundles : Array (Option TraceBundle) :=
  #[none, none]

private def rgFinal : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .resolution (.arith #[⟨1, false⟩] #[])], #[]⟩

/-- End-to-end: the definite-disc refutation walked from the positive
root-atom input clause. -/
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩]], clauseHolds ρ rgAtoms C) → False := by
  nlsat_refute ⟨rgAtoms, rgClauses, rgBundles, rgFinal⟩

private def rgAtomsBad : Array (Option Atom) :=
  #[none,
   some (.root ⟨.eq, 0, 0, [(1, [(0, 2)]), (1, [])]⟩)]

/- Negative probe: `i = 0` keeps the count bound live, the close
stays gated; rejection is sound. -/
#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩]], clauseHolds ρ rgAtomsBad C) → False := by
  nlsat_refute ⟨rgAtomsBad, rgClauses, rgBundles, rgFinal⟩

/-! ## G4 census item 3 — the cross-links member, end-to-end through
the walk

Root bounds (`¬` literals in the clause) give OPAQUE `rootVal`
comparisons; the arith lemma cannot close from the literals alone and
NEEDS the bundle's thomQuadratic steps to transfer, via the Coverage
iff, into the evaluated Thom region formulas. p = x0²−2; inputs
`ρ 0 > root₁(p)`, `ρ 0 < root₂(p)`, `p ≥ 0` — empty jointly. -/

private def xlPm2 : MPoly := [(1, [(0, 2)]), (-2, [])]

private def xlAtoms : Array (Option Atom) :=
  #[none,
   some (.root ⟨.gt, 0, 1, xlPm2⟩),
   some (.root ⟨.lt, 0, 2, xlPm2⟩),
   some (.ineq ⟨.lt, [(xlPm2, false)]⟩)]

private def xlClauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false },
   { lits := #[⟨2, false⟩], learned := false, deleted := false },
   { lits := #[⟨3, true⟩], learned := false, deleted := false }]

private def xlBundles : Array (Option TraceBundle) := #[none, none, none, none]

private def xlFinal : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .cellBound .lower .gt 0 1 xlPm2, .thomQuadratic .gt 0 1 xlPm2 1 1 1 (-1),
      .resolution (.clause 2),
      .cellBound .upper .lt 0 2 xlPm2, .thomQuadratic .lt 0 2 xlPm2 1 1 0 (-1),
      .resolution (.clause 3),
      .resolution (.arith #[⟨1, false⟩, ⟨2, false⟩, ⟨3, true⟩] #[])], #[]⟩

example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, false⟩], [⟨3, true⟩]],
      clauseHolds ρ xlAtoms C) → False := by
  nlsat_refute ⟨xlAtoms, xlClauses, xlBundles, xlFinal⟩

/- Load-bearing: dropping the thomQuadratic steps leaves only the
opaque bounds; the arith discharge fails, and the walk rejects. -/
private def xlFinalNoSteps : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .cellBound .lower .gt 0 1 xlPm2,
      .resolution (.clause 2),
      .cellBound .upper .lt 0 2 xlPm2,
      .resolution (.clause 3),
      .resolution (.arith #[⟨1, false⟩, ⟨2, false⟩, ⟨3, true⟩] #[])], #[]⟩

#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, false⟩], [⟨3, true⟩]],
      clauseHolds ρ xlAtoms C) → False := by
  nlsat_refute ⟨xlAtoms, xlClauses, xlBundles, xlFinalNoSteps⟩

/- Grammar-gate probe (precheck): `sq = 0` with `sp = −1` breaks the
E1-pinned `sq = 0 → sp = 0` grammar condition — the bundle's steps
fail `grammarOK` and the walk rejects at `precheck` (before any
discharge work). -/
private def xlFinalGrammarBad : TraceBundle :=
  ⟨#[.resolution (.clause 1),
      .cellBound .lower .gt 0 1 xlPm2, .thomQuadratic .gt 0 1 xlPm2 0 1 1 (-1),
      .resolution (.clause 2),
      .resolution (.clause 3),
      .resolution (.arith #[⟨1, false⟩, ⟨2, false⟩, ⟨3, true⟩] #[])], #[]⟩

#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, false⟩], [⟨3, true⟩]],
      clauseHolds ρ xlAtoms C) → False := by
  nlsat_refute ⟨xlAtoms, xlClauses, xlBundles, xlFinalGrammarBad⟩


/-! ## ordering_139 — the L1-open specimen walked end-to-end (post-writeback-fix)

Machine-generated snapshot (scratch_dump.lean `goO139`, 2026-08-10):
the 6-var transitivity-of-fractions problem
`a·db ≤ b·da, b·dc ≤ c·db, da/db/dc > 0 ⊢ a·dc ≤ c·da` refuted by the
solver in 6 conflicts (z3-4.12.5's exact count). Trace in INTERNAL
variable order (reorder live). What it exercises for the first time on
a REAL refutation (not synthetic fixtures): a production `rootGeneric`
step (deg-1 with vanishing-lc at the sample — the census's predicted
reachable case), production cellBound/linearRoot cross-links feeding
`collectStepFacts`, factorSplit bundles, a 5-learned-clause RUP DAG
with pure-resolution nodes, and all six input clauses referenced.
-/

private def o139Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.gt, [([((-1), [(0, 1), (4, 1)]), (1, [(1, 1), (3, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([((-1), [(1, 1), (5, 1)]), (1, [(2, 1), (4, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(1, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(2, 1)])], false)]⟩),
   some (.ineq ⟨.gt, [([((-1), [(0, 1), (5, 1)]), (1, [(2, 1), (3, 1)])], false)]⟩),
   some (.root ⟨.gt, 4, 1, [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])]⟩),
   some (.ineq ⟨.eq, [([(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])], false)]⟩)]

private def o139Clauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, true⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩], learned := false, deleted := false },
   { lits := #[⟨3, false⟩], learned := false, deleted := false },
   { lits := #[⟨4, false⟩], learned := false, deleted := false },
   { lits := #[⟨5, false⟩], learned := false, deleted := false },
   { lits := #[⟨6, false⟩], learned := false, deleted := false },
   { lits := #[⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩, ⟨7, true⟩], learned := true, deleted := false },
   { lits := #[⟨3, true⟩, ⟨4, true⟩, ⟨8, true⟩], learned := true, deleted := false },
   { lits := #[⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩], learned := true, deleted := false },
   { lits := #[⟨3, true⟩, ⟨4, true⟩], learned := true, deleted := false },
   { lits := #[⟨3, true⟩], learned := true, deleted := false }]

private def o139Bundles : Array (Option TraceBundle) :=
  #[none,
   none,
   none,
   none,
   none,
   none,
   none,
   some ⟨#[.resolution (.clause 6),
      .factorSplit [((-1), [(1, 1)])] #[[((-1), [(1, 1)])]] #[],
      .factorSplit [((-1), [(0, 1)])] #[[((-1), [(0, 1)])]] #[],
      .factorSplit [(1, [(0, 1), (2, 1), (4, 1)]), ((-1), [(1, 1), (2, 1), (3, 1)])] #[[(1, [(2, 1)])], [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])]] #[],
      .rootGeneric .gt 4 1 [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])],
      .cellBound .lower .gt 4 1 [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])],
      .factorSplit [(1, [(0, 1)])] #[[(1, [(0, 1)])]] #[],
      .linearRoot .gt 2 [(1, [(2, 1)])] false none,
      .cellBound .lower .gt 2 1 [(1, [(2, 1)])],
      .linearRoot .gt 1 [((-1), [(1, 1)])] true none,
      .cellBound .lower .gt 1 1 [((-1), [(1, 1)])],
      .linearRoot .gt 0 [((-1), [(0, 1)])] true none,
      .cellBound .lower .gt 0 1 [((-1), [(0, 1)])],
      .resolution (.arith #[⟨2, true⟩, ⟨6, false⟩] #[⟨7, true⟩, ⟨5, true⟩, ⟨4, true⟩, ⟨3, true⟩]),
      .resolution (.clause 2)], #[⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩, ⟨7, true⟩]⟩,
   some ⟨#[.resolution (.clause 6),
      .factorSplit [((-1), [(1, 1)])] #[[((-1), [(1, 1)])]] #[],
      .factorSplit [((-1), [(0, 1)])] #[[((-1), [(0, 1)])]] #[],
      .factorSplit [(1, [(0, 1), (2, 1), (4, 1)]), ((-1), [(1, 1), (2, 1), (3, 1)])] #[[(1, [(2, 1)])], [(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])]] #[[(1, [(0, 1), (4, 1)]), ((-1), [(1, 1), (3, 1)])]],
      .linearRoot .gt 1 [((-1), [(1, 1)])] true none,
      .cellBound .lower .gt 1 1 [((-1), [(1, 1)])],
      .linearRoot .gt 0 [((-1), [(0, 1)])] true none,
      .cellBound .lower .gt 0 1 [((-1), [(0, 1)])],
      .resolution (.arith #[⟨2, true⟩, ⟨6, false⟩] #[⟨8, true⟩, ⟨4, true⟩, ⟨3, true⟩]),
      .resolution (.clause 2)], #[⟨3, true⟩, ⟨4, true⟩, ⟨8, true⟩]⟩,
   some ⟨#[.resolution (.clause 8),
      .factorSplit [((-1), [(0, 1)])] #[[((-1), [(0, 1)])]] #[],
      .factorSplit [(1, [(0, 1)])] #[[(1, [(0, 1)])]] #[],
      .linearRoot .gt 0 [((-1), [(0, 1)])] true none,
      .cellBound .lower .gt 0 1 [((-1), [(0, 1)])],
      .resolution (.arith #[⟨1, true⟩, ⟨8, true⟩, ⟨7, true⟩] #[⟨3, true⟩]),
      .resolution (.clause 7),
      .resolution (.clause 1)], #[⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩]⟩,
   some ⟨#[.resolution (.clause 9),
      .resolution (.clause 5)], #[⟨3, true⟩, ⟨4, true⟩]⟩,
   some ⟨#[.resolution (.clause 10),
      .resolution (.clause 4)], #[⟨3, true⟩]⟩]

private def o139Final : TraceBundle :=
  ⟨#[.resolution (.clause 11),
      .resolution (.clause 3)], #[]⟩

/-- End-to-end: the ordering_139 refutation walked from all six
referenced input clauses. (Positive since the G11 lane — cid 7's
arith member consumes the production `rootGeneric` deg-1 non-const-lc
step through `linearRootNonconstPos_discharge`.) -/
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, true⟩], [⟨2, true⟩], [⟨3, false⟩], [⟨4, false⟩],
      [⟨5, false⟩], [⟨6, false⟩]], clauseHolds ρ o139Atoms C) → False := by
  nlsat_refute ⟨o139Atoms, o139Clauses, o139Bundles, o139Final⟩

/-! ## 19b Slice 3 — pd1 walked end-to-end (the pseudoDivision gate lift)

Machine-generated snapshot (scratch_dump.lean `goPd1`, regenerated
2026-08-13 post-gate-lift): the canonical Jovanović core
`{x1 − x0² = 0, x1 < 0}`. The solver learns `x0² < 0` (atom 3 — the
path-(e) rebuilt literal) off
`pseudoDivision x1 (x1−x0²) 1 1 x0² 1 false` — exactly the
Slice-0-pinned payload (const lc, d = 1 odd, remainder x0²) — then the
final bundle's `leafNumeric` kills it. This is the first production
bundle carrying a pseudoDivision step through `precheck`: the gate
lift is witnessed by this walk. -/

private def pd1Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(1, 1)]), ((-1), [(0, 2)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(1, 1)])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 2)])], false)]⟩)]

private def pd1Clauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false },
   { lits := #[⟨2, false⟩], learned := false, deleted := false },
   { lits := #[⟨3, false⟩], learned := true, deleted := false }]

private def pd1Bundles : Array (Option TraceBundle) :=
  #[none,
   none,
   none,
   some ⟨#[.resolution (.clause 2),
      .pseudoDivision [(1, [(1, 1)])] [(1, [(1, 1)]), ((-1), [(0, 2)])] 1 1 [(1, [(0, 2)])] 1 false,
      .resolution (.arith #[⟨1, false⟩, ⟨2, false⟩] #[⟨3, false⟩]),
      .resolution (.clause 1)], #[⟨3, false⟩]⟩]

private def pd1Final : TraceBundle :=
  ⟨#[.resolution (.clause 3),
      .leafNumeric 0,
      .resolution (.arith #[⟨3, false⟩] #[])], #[]⟩

/- Gate pins (native): the pd1 learned bundle is v0 post-lift (19b
Slice 3); an intBranch bundle is v0 too (12e — the last shape gate
lifted; only the S1 fragment gate remains). -/
#guard (pd1Bundles[3]!).get!.isV0 == true
#guard (TraceBundle.mk #[.intBranch 0 7] #[]).isV0 == true

/-- End-to-end: pd1 walked from both input clauses. The learned clause
IS the rebuilt literal `x0² < 0`; its arith member is discharged with
the bundle's pd step available to the Slice-2 transport, and the final
member (`x0² < 0 ⊢ ⊥`) closes off `leafNumeric`. -/
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, false⟩]], clauseHolds ρ pd1Atoms C) → False := by
  nlsat_refute ⟨pd1Atoms, pd1Clauses, pd1Bundles, pd1Final⟩

/- Glue-subsumption at walk level (the RefuteTests pins cover the
Refute level): dropping the pd step from bundle 3 leaves the arith
member to the F2 glue (sq_nonneg + eq substitution) — the walk still
closes. -/
private def pd1BundlesStepFree : Array (Option TraceBundle) :=
  #[none,
   none,
   none,
   some ⟨#[.resolution (.clause 2),
      .resolution (.arith #[⟨1, false⟩, ⟨2, false⟩] #[⟨3, false⟩]),
      .resolution (.clause 1)], #[⟨3, false⟩]⟩]

example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, false⟩]], clauseHolds ρ pd1Atoms C) → False := by
  nlsat_refute ⟨pd1Atoms, pd1Clauses, pd1BundlesStepFree, pd1Final⟩

/- Corrupt remainder (grammar-CLEAN — r = x0²+1 still has
`degreeIn x1 r = 0 < 1` — but the ring identity is false): the
transport's `pseudoDivisionIdentity` throws, the step is skipped
soundly, and the walk still closes on the glue. Pin: corrupted
payloads degrade to the glue, never to unsoundness. -/
private def pd1BundlesCorruptR : Array (Option TraceBundle) :=
  #[none,
   none,
   none,
   some ⟨#[.resolution (.clause 2),
      .pseudoDivision [(1, [(1, 1)])] [(1, [(1, 1)]), ((-1), [(0, 2)])] 1 1 [(1, [(0, 2)]), (1, [])] 1 false,
      .resolution (.arith #[⟨1, false⟩, ⟨2, false⟩] #[⟨3, false⟩]),
      .resolution (.clause 1)], #[⟨3, false⟩]⟩]

example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, false⟩]], clauseHolds ρ pd1Atoms C) → False := by
  nlsat_refute ⟨pd1Atoms, pd1Clauses, pd1BundlesCorruptR, pd1Final⟩

/- Grammar-gate probe (precheck): `lcSign = 2` breaks the pd grammar
(`lcSign ∈ {−1, 0, 1}`) — the bundle's steps fail `grammarOK` and the
walk rejects at `precheck`, before any discharge work. Pre-lift this
was masked by the isV0 reject firing first; post-lift the grammar gate
is a pd bundle's first line of defense. -/
private def pd1BundlesGrammarBad : Array (Option TraceBundle) :=
  #[none,
   none,
   none,
   some ⟨#[.resolution (.clause 2),
      .pseudoDivision [(1, [(1, 1)])] [(1, [(1, 1)]), ((-1), [(0, 2)])] 1 1 [(1, [(0, 2)])] 2 false,
      .resolution (.arith #[⟨1, false⟩, ⟨2, false⟩] #[⟨3, false⟩]),
      .resolution (.clause 1)], #[⟨3, false⟩]⟩]

#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩], [⟨2, false⟩]], clauseHolds ρ pd1Atoms C) → False := by
  nlsat_refute ⟨pd1Atoms, pd1Clauses, pd1BundlesGrammarBad, pd1Final⟩

/-! ## 12e — int1 walked end-to-end (integer B&B; the last shape gate lifted)

Machine-generated snapshot (scratch_dump.lean `goInt1`, 2026-08-13):
`{x0² = 2}` over one INTEGER variable — UNSAT over ℤ, SAT over ℝ.
The solver takes TWO B&B rounds (z3 `search_check`'s loop): the first
witness lands near −√2 → `.intBranch 0 (-2)` (clause 2: `{x0 ≤ −2,
x0 ≥ −1}`), restart; the second near +√2 → `.intBranch 0 1` (clause 3:
`{x0 ≤ 1, x0 ≥ 2}`), restart; refutation. The branch clauses are
INPUT-flagged (`learned = false` — z3's `mk_clause(…, false, nullptr)`)
but carry bundles, so the walk's contract counts only clause 1 (the
eq) as an input. The final bundle's three arith members mix branch
literals with the eq (leafNumeric univariate conflicts). -/

private def int1Atoms : Array (Option Atom) :=
  #[none,
   some (.ineq ⟨.eq, [([(1, [(0, 2)]), ((-2), [])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)]), (2, [])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)]), (1, [])], false)]⟩),
   some (.ineq ⟨.gt, [([(1, [(0, 1)]), ((-1), [])], false)]⟩),
   some (.ineq ⟨.lt, [([(1, [(0, 1)]), ((-2), [])], false)]⟩)]

private def int1Clauses : Array Clause :=
  #[{ lits := #[⟨0, false⟩], learned := false, deleted := false },
   { lits := #[⟨1, false⟩], learned := false, deleted := false },
   { lits := #[⟨2, true⟩, ⟨3, true⟩], learned := false, deleted := false },
   { lits := #[⟨4, true⟩, ⟨5, true⟩], learned := false, deleted := false }]

private def int1Bundles : Array (Option TraceBundle) :=
  #[none,
   none,
   some ⟨#[.intBranch 0 (-2)], #[⟨2, true⟩, ⟨3, true⟩]⟩,
   some ⟨#[.intBranch 0 1], #[⟨4, true⟩, ⟨5, true⟩]⟩]

private def int1Final : TraceBundle :=
  ⟨#[.resolution (.clause 3),
      .leafNumeric 0,
      .resolution (.arith #[⟨5, true⟩, ⟨1, false⟩] #[]),
      .leafNumeric 0,
      .resolution (.arith #[⟨3, true⟩, ⟨1, false⟩, ⟨4, true⟩] #[]),
      .resolution (.clause 2),
      .leafNumeric 0,
      .resolution (.arith #[⟨1, false⟩, ⟨2, true⟩] #[]),
      .resolution (.clause 1)], #[]⟩

/-- End-to-end: int1 walked from the single input clause (the eq);
the context's integrality hypothesis discharges both branch splits
(12e decision 1). -/
example : ∀ ρ : Nat → ℝ, (∃ n : ℤ, ρ 0 = (n : ℝ)) →
    (∀ C ∈ [[⟨1, false⟩]], clauseHolds ρ int1Atoms C) → False := by
  nlsat_refute ⟨int1Atoms, int1Clauses, int1Bundles, int1Final⟩

/- Missing-integrality probe: the same walk WITHOUT the `∃ n : ℤ`
hypothesis must reject — the branch splits are only valid at integral
`ρ 0` (the goal is in fact unprovable without it: `ρ 0 = √2`
satisfies the input clause). Sound rejection at the intBranch
discharge. -/
#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ,
    (∀ C ∈ [[⟨1, false⟩]], clauseHolds ρ int1Atoms C) → False := by
  nlsat_refute ⟨int1Atoms, int1Clauses, int1Bundles, int1Final⟩

/- Wrong-variable integrality probe: an `∃ n : ℤ` hyp for a DIFFERENT
variable (ρ 1 — not even present in the problem) does not discharge
the split on ρ 0 — the per-variable matching is load-bearing. -/
#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ, (∃ n : ℤ, ρ 1 = (n : ℝ)) →
    (∀ C ∈ [[⟨1, false⟩]], clauseHolds ρ int1Atoms C) → False := by
  nlsat_refute ⟨int1Atoms, int1Clauses, int1Bundles, int1Final⟩

/- Payload-mismatch probe (F-w): `lo = 5` with the clause still
carrying `x ≤ −2 ∨ x ≥ −1` — the by-value decode rejects (the gt
atom's poly is not `x − 5`). Note a garbage `lo` would still be a
VALID split mathematically; this rejection is the clause/payload
agreement gate (trace-shape fidelity), not soundness. -/
private def int1BundlesBadLo : Array (Option TraceBundle) :=
  #[none,
   none,
   some ⟨#[.intBranch 0 5], #[⟨2, true⟩, ⟨3, true⟩]⟩,
   some ⟨#[.intBranch 0 1], #[⟨4, true⟩, ⟨5, true⟩]⟩]

#guard_msgs (drop error) in
example : ∀ ρ : Nat → ℝ, (∃ n : ℤ, ρ 0 = (n : ℝ)) →
    (∀ C ∈ [[⟨1, false⟩]], clauseHolds ρ int1Atoms C) → False := by
  nlsat_refute ⟨int1Atoms, int1Clauses, int1BundlesBadLo, int1Final⟩
end LeanNonlinearArith.Nlsat.Tests.Walk