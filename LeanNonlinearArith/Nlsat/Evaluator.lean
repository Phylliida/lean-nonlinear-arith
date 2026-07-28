import LeanNonlinearArith.Nlsat.AnumEval
import LeanNonlinearArith.Nlsat.IntervalSet

/-!
# nla-12b-ii — evaluator assembly: `evalSignAt` + `isolateRootsAt` + signs

Port of the three anum entry points the nlsat evaluator consumes
(DESIGN-nlsat-quadratic §4b; Z3-shape per Danielle's decision):

* `evalSignAt` — `algebraic_numbers.cpp:2246`: optimistic all-rational
  pass → rational-fragment substitution → magnitude-gated interval
  refinement → exact resultant zero test: `R(y) = Res(y − p′, qᵢ…)`
  with `L = 2^{−k}` from `nonzeroRootLowerBound`, then refine until the
  enclosure excludes zero or fits in `(−L, L)`. nla-28 threading: the
  (possibly refined) assignment is returned alongside the sign;
  `save_intervals::restore_if_too_small` semantics ported (cells
  refined below `minMagnitude` during the FINAL loop are restored to
  their post-interval-pass state; the interval pass's own refinements
  stick). `m_zero_accuracy = 0` (default) ⇒ the approximate-zero
  shortcut is dead, as in default Z3.
* `isolateRootsAt` — `:2547`: zero/const/univariate shortcuts →
  substitute rationals → resultant-eliminate each algebraic variable
  with its defining poly (vars sorted by defining-poly degree, stable)
  → kernel isolation → `filter_roots` by `evalSignAt = 0`. The
  `q ≡ 0` degenerate fallbacks (linear-coeff solve, auxiliary-z nested
  path) need anum VALUES (op-by-op anum arithmetic) — **boarded as
  nla-29** (Danielle 2026-07-28: full anum-arithmetic arc first, then
  the fallbacks with z3's exact mechanism); they currently return
  `none` (unreachable until the solver hits a degenerate trace).
* `isolateRootsSigns` — `:2902`: refine roots to `DEFAULT_PRECISION = 2`
  and `evalSignAt` at `intLt`/`select`/`intGt` sample points between
  consecutive roots (all unassigned vars mapped to the sample, z3
  `ext2_var2num`; samples are always rational).

The evaluator layer (`SignTable`, atom predicates, `infeasible_intervals`
— `nlsat_evaluator.cpp`) lives in `Nlsat/EvaluatorTable.lean`.

**Untrusted** (same trust shape as the rest of the search side).
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-- Partial assignment of algebraic values (z3 `polynomial::var2anum`).
Refinements thread through per nla-28 (z3 mutates the stored cells). -/
abbrev Assignment := Array (Var × RAlg)

namespace Assignment

def get? (σ : Assignment) (x : Var) : Option RAlg :=
  σ.foldl (fun acc (y, v) => if y == x then some v else acc) none

def contains (σ : Assignment) (x : Var) : Bool := (σ.get? x).isSome

/-- z3-style store: replace the binding if present, else extend
(`ext_var2num` shape). -/
def set (σ : Assignment) (x : Var) (v : RAlg) : Assignment :=
  if σ.contains x then σ.map fun (y, w) => if y == x then (y, v) else (y, w)
  else σ.push (x, v)

/-- `undef_var_assignment`: the assignment with `x` removed. -/
def erase (σ : Assignment) (x : Var) : Assignment :=
  σ.filter (·.1 != x)

end Assignment

namespace MPoly

/-- Sorted unique variables of `p` (z3 `manager::vars`). -/
def vars (p : MPoly) : Array Var :=
  let collected := p.foldl (fun acc (_, m) =>
    m.foldl (fun acc (x, _) => if acc.contains x then acc else acc.push x) acc) #[]
  collected.qsort (· < ·)

end MPoly

namespace AnumEval

/-- Sign of an integer as −1/0/1 (z3 `to_sign`). -/
def signOfInt (v : Int) : Int := if v < 0 then -1 else if v == 0 then 0 else 1

/-- Degree of an assigned value (z3 `imp::degree`, used by
`var_degree_lt`): 0 for zero, 1 for basic, `deg p` for cells. -/
def valueDegree : RAlg → Nat
  | .rat q => if q == 0 then 0 else 1
  | .root p _ _ _ => p.size - 1

/-- Stable insertion sort by defining-polynomial degree (z3
`std::stable_sort(xs, var_degree_lt)`): assigned vars by `imp::degree`,
UNASSIGNED vars as `UINT_MAX` (they sort last — the isolation target
lands at the back). Order matters: the resultant chain's numbers
depend on elimination order. -/
def sortByValueDegree (σ : Assignment) (xs : Array Var) : Array Var := Id.run do
  let degOf := fun (x : Var) => match σ.get? x with
    | some v => valueDegree v
    | none => 0xffffffff   -- z3 UINT_MAX for unassigned
  let mut out : Array Var := #[]
  for x in xs do
    let dx := degOf x
    let mut inserted := false
    let mut next : Array Var := #[]
    for y in out do
      if !inserted && dx < degOf y then
        next := next.push x
        inserted := true
      next := next.push y
    if !inserted then
      next := next.push x
    out := next
  return out

/-- z3 `eval_sign_at` (`algebraic_numbers.cpp:2246`). `defQ`, when
given, supplies a rational value for variables not in `σ` (z3
`ext2_var2num` — used by the signs variant's sample points; the
default joins the rational fragment, exactly as z3's basic default
does). Returns the sign AND the threaded assignment (nla-28). -/
def evalSignAt (p : MPoly) (σ : Assignment) (defQ : Option Rat := none) :
    Int × Assignment := Id.run do
  let mut σ := σ
  let lkup := fun (s : Assignment) (x : Var) => (s.get? x) <|> (defQ.map RAlg.rat)
  let mut result : Option Int := none
  let mut restart := true
  while restart do
    restart := false
    -- Optimistic pass: maybe everything is rational
    let pVars := p.vars
    if pVars.all fun x => match lkup σ x with | some (.rat _) => true | _ => false then
      let v := p.evalRat fun x => match lkup σ x with | some (.rat q) => q | _ => 0
      result := some (signOfInt (if v < 0 then -1 else if v == 0 then 0 else 1))
    else
      -- Eliminate the rational fragment
      let mut p' := p
      for x in pVars do
        match lkup σ x with
        | some (.rat q) => p' := p'.substRat x q
        | _ => pure ()
      if p'.isZero then
        result := some 0
      else
        match p'.asConst? with
        | some c => result := some (signOfInt c)
        | none =>
          let xs := p'.vars
          let cellI := fun (s : Assignment) (x : Var) => match s.get? x with
            | some (.root _ a b _) => (⟨a, b⟩ : MpbqI)
            | _ => ⟨Mpbq.ofInt 0, Mpbq.ofInt 0⟩   -- unreachable: rationals substituted
          -- Interval pass: refine (magnitude-gated) while the enclosure straddles 0
          let mut ri := p'.evalInterval (cellI σ)
          let mut phaseDone := false
          while !phaseDone && !restart do
            if !ri.containsZero then
              result := some (if ri.isPos then 1 else -1)
              phaseDone := true
            else
              let mut anyRefined := false
              for x in xs do
                match σ.get? x with
                | some v@(.root _ _ _ _) =>
                  if RAlg.magnitude v > RAlg.minMagnitude then
                    let v' := RAlg.refine1 v
                    σ := σ.set x v'
                    match v' with
                    | .rat _ => restart := true   -- became basic: restart all
                    | _ => anyRefined := true
                | _ => pure ()
              if !anyRefined && !restart then
                phaseDone := true
              else if !restart then
                ri := p'.evalInterval (cellI σ)
          -- Exact zero test via resultants
          if !restart && result.isNone then
            let y := (xs.foldl (fun acc x => max acc x) 0) + 1
            let xsSorted := sortByValueDegree σ xs
            let mut bigR := MPoly.sub (MPoly.ofVar y) p'
            for x in xsSorted do
              match σ.get? x with
              | some (.root qp _ _ _) => bigR := resultantElim bigR x qp
              | _ => pure ()
            let k := match bigR.toQPoly? y with
              | some qR => nonzeroRootLowerBound qR
              | none => 0   -- unreachable: R is univariate in y
            let lM : Mpbq := Mpbq.mk (-1) k
            let uM : Mpbq := Mpbq.mk 1 k
            let inRange := fun (i : MpbqI) => Mpbq.lt lM i.lo && Mpbq.lt i.hi uM
            if inRange ri then
              result := some 0
            else
              -- save the cells (z3 save_intervals) before the final loop
              let saved := xs.map fun x => (x, σ.get? x)
              let mut finalDone := false
              while !finalDone && !restart do
                ri := p'.evalInterval (cellI σ)
                if !ri.containsZero then
                  result := some (if ri.isPos then 1 else -1)
                  finalDone := true
                else if inRange ri then
                  result := some 0
                  finalDone := true
                else
                  for x in xs do
                    match σ.get? x with
                    | some v@(.root _ _ _ _) =>
                      let v' := RAlg.refine1 v
                      σ := σ.set x v'
                      match v' with
                      | .rat _ => restart := true
                      | _ => pure ()
                    | _ => pure ()
              -- restore_if_too_small (on every exit of the resultant phase)
              for (x, sv) in saved do
                match σ.get? x, sv with
                | some v@(.root _ _ _ _), some sv' =>
                  if RAlg.magnitude v < RAlg.minMagnitude then
                    σ := σ.set x sv'
                | _, _ => pure ()
  return (result.getD 0, σ)

/-- z3 `isolate_roots` under partial assignment (`algebraic_numbers.cpp:2547`).
`none` marks the `q ≡ 0` degenerate fallback (linear-coeff solve /
auxiliary-z) — boarded as **nla-29** (needs anum arithmetic; Danielle
2026-07-28). `nested` is the recursive-call flag (z3 SASSERTs the
degenerate case can't recur there). -/
def isolateRootsAt (p : MPoly) (σ : Assignment) (nested : Bool := false) :
    Option (Array RAlg) × Assignment := Id.run do
  let _ := nested
  if p.isZero || p.asConst?.isSome then
    return (some #[], σ)
  -- univariate shortcut: isolate directly in its only variable
  if p.vars.size == 1 then
    let x := p.vars[0]!
    match p.toQPoly? x with
    | some q => return (some (RAlg.isolateRoots q), σ)
    | none => return (some #[], σ)   -- unreachable
  -- eliminate the rational fragment
  let mut p' := p
  for x in p.vars do
    match σ.get? x with
    | some (.rat q) => p' := p'.substRat x q
    | _ => pure ()
  if p'.isZero || p'.asConst?.isSome then
    return (some #[], σ)
  if p'.vars.size == 1 then
    let x := p'.vars[0]!
    if σ.contains x then
      -- the unassigned variable vanished under substitution: no roots
      return (some #[], σ)
    match p'.toQPoly? x with
    | some q => return (some (RAlg.isolateRoots q), σ)
    | none => return (some #[], σ)   -- unreachable
  -- sort variables by the degree of the values; the target is last
  let xs := sortByValueDegree σ p'.vars
  let x := xs.back!
  if σ.contains x then
    return (some #[], σ)
  -- resultant-eliminate every assigned algebraic variable
  let mut q := p'
  for y in xs[:xs.size - 1] do
    if !q.isZero then
      match σ.get? y with
      | some (.root qp _ _ _) => q := resultantElim q y qp
      | _ => pure ()
  if q.isZero then
    -- q ≡ 0 fallback (nla-29: linear-coeff solve / auxiliary-z)
    return (none, σ)
  if q.asConst?.isSome then
    return (some #[], σ)
  -- isolate the univariate q and filter candidates by exact sign
  match q.toQPoly? x with
  | none => return (some #[], σ)   -- unreachable: q is univariate in x
  | some qq =>
    let mut σ := σ
    let mut kept : Array RAlg := #[]
    for r in RAlg.isolateRoots qq do
      let (s, σ') := evalSignAt p' (σ.set x r)
      σ := σ'
      match σ.get? x with
      | some r' => if s == 0 then kept := kept.push r'
      | none => pure ()
    return (some kept, σ)

/-- z3's `DEFAULT_PRECISION` (`algebraic_numbers.cpp:2900`). -/
def defaultPrecision : Nat := 2

/-- The signs variant (`algebraic_numbers.cpp:2902`): roots of `p` under
`σ` plus the sign of `p` on every cell they cut the line into —
`numRoots + 1` signs (or a single sign when there are no roots).
Samples: `intLt` below, `select` between, `intGt` above; every
unassigned variable takes the sample (z3 `ext2_var2num`). -/
def isolateRootsSigns (p : MPoly) (σ : Assignment) :
    Option (Array RAlg × Array Int) × Assignment := Id.run do
  let (roots?, σ) := isolateRootsAt p σ
  match roots? with
  | none => return (none, σ)
  | some roots =>
    if roots.isEmpty then
      let (s, σ) := evalSignAt p σ (some 0)
      return (some (#[], #[s]), σ)
    let mut roots := roots.map (RAlg.refineUntilPrec · defaultPrecision)
    let mut signs : Array Int := #[]
    let mut σ := σ
    let (lo, r0') := RAlg.intLt roots[0]!
    roots := roots.set! 0 r0'
    let (s0, σ0) := evalSignAt p σ (some (mkRat lo 1))
    σ := σ0
    signs := signs.push s0
    for i in [1:roots.size] do
      let (w, pi, ci) := RAlg.select roots[i - 1]! roots[i]!
      roots := (roots.set! (i - 1) pi).set! i ci
      let (s, σ') := evalSignAt p σ (some w)
      σ := σ'
      signs := signs.push s
    let (hi, rl') := RAlg.intGt roots[roots.size - 1]!
    roots := roots.set! (roots.size - 1) rl'
    let (sN, σN) := evalSignAt p σ (some (mkRat hi 1))
    σ := σN
    signs := signs.push sN
    return (some (roots, signs), σ)

end AnumEval

end LeanNonlinearArith.Nlsat
