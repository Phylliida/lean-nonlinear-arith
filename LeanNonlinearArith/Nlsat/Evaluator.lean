import LeanNonlinearArith.Nlsat.AnumEval
import LeanNonlinearArith.Nlsat.IntervalSet
import LeanNonlinearArith.Kernel.AnumArith

/-!
# nla-12b-ii — evaluator assembly: `evalSignAt` + `isolateRootsAt` + signs

Port of the three anum entry points the nlsat evaluator consumes
(DESIGN-nlsat-quadratic §4b; Z3-shape per Danielle's decision):

* `evalSignAt` — `algebraic_numbers.cpp:2246`: optimistic all-rational
  pass → rational-fragment substitution → magnitude-gated interval
  refinement → exact resultant zero test: `R(y) = Res(y − p′, qᵢ…)`
  with `L = 2^{−k}` from `nonzeroRootLowerBound`, then refine until the
  enclosure excludes zero or fits in `(−L, L)`. Runs in `CellM`:
  refinements persist in the store exactly as z3's in-place mutation;
  `save_intervals::restore_if_too_small` semantics ported (cells
  refined below `minMagnitude` during the FINAL loop are restored to
  their post-interval-pass values; the interval pass's own refinements
  stick). `m_zero_accuracy = 0` (default) ⇒ the approximate-zero
  shortcut is dead, as in default Z3.
* `isolateRootsAt` — `:2547`: zero/const/univariate shortcuts →
  substitute rationals → resultant-eliminate each algebraic variable
  with its defining poly (vars sorted by defining-poly degree, stable,
  unassigned as UINT_MAX) → kernel isolation → `filter_roots` by
  `evalSignAt = 0`. The `q ≡ 0` degenerate fallbacks need anum VALUES
  (op-by-op anum arithmetic) — **boarded as nla-29** (Danielle
  2026-07-28); they currently return `none`.
* `isolateRootsSigns` — `:2902`: refine roots to `DEFAULT_PRECISION = 2`
  and `evalSignAt` at `intLt`/`select`/`intGt` sample points between
  consecutive roots (all unassigned vars mapped to the sample, z3
  `ext2_var2num`; samples are always rational).

The evaluator layer (`SignTable`, atom predicates, `infeasible_intervals`)
lives in `Nlsat/EvaluatorTable.lean`.

**Untrusted** (same trust shape as the rest of the search side).
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-- Partial assignment of algebraic values (z3 `polynomial::var2anum`):
bindings from variables to store cells. z3's `undef_var_assignment` and
`ext_var2num` SHARE the underlying cell heap — here that is literal:
`erase`/`set` touch bindings only, never the store. -/
abbrev Assignment := Array (Var × CellId)

namespace Assignment

def get? (σ : Assignment) (x : Var) : Option CellId :=
  σ.foldl (fun acc (y, v) => if y == x then some v else acc) none

def contains (σ : Assignment) (x : Var) : Bool := (σ.get? x).isSome

/-- z3-style store: replace the binding if present, else extend
(`ext_var2num` shape). -/
def set (σ : Assignment) (x : Var) (v : CellId) : Assignment :=
  if σ.contains x then σ.map fun (y, w) => if y == x then (y, v) else (y, w)
  else σ.push (x, v)

/-- `undef_var_assignment`: the assignment with `x` removed. -/
def erase (σ : Assignment) (x : Var) : Assignment :=
  σ.filter (·.1 != x)

/-- Build an assignment from fresh cell values (test/construction path). -/
def ofValues (l : List (Var × RAlg)) : CellM Assignment := do
  let mut σ : Assignment := #[]
  for (x, v) in l do
    σ := σ.push (x, ← CellStore.fresh v)
  return σ

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
def sortByValueDegree (σ : Assignment) (xs : Array Var) : CellM (Array Var) := do
  let mut tagged : Array (Var × Nat) := #[]
  for x in xs do
    match σ.get? x with
    | some c => tagged := tagged.push (x, valueDegree (← CellStore.read c))
    | none => tagged := tagged.push (x, 0xffffffff)   -- z3 UINT_MAX for unassigned
  let mut out : Array (Var × Nat) := #[]
  for xt in tagged do
    let mut inserted := false
    let mut next : Array (Var × Nat) := #[]
    for yt in out do
      if !inserted && xt.2 < yt.2 then
        next := next.push xt
        inserted := true
      next := next.push yt
    if !inserted then
      next := next.push xt
    out := next
  return out.map (·.1)

/-- z3 `eval_sign_at` (`algebraic_numbers.cpp:2246`). `defQ`, when
given, supplies a rational value for variables not in `σ` (z3
`ext2_var2num` — used by the signs variant's sample points; the
default joins the rational fragment, exactly as z3's basic default
does). Refinements persist in the store (nla-28 semantics, now
structural). -/
def evalSignAt (p : MPoly) (σ : Assignment) (defQ : Option Rat := none) : CellM Int := do
  let readQ (x : Var) : CellM (Option Rat) := do
    match σ.get? x with
    | some c => match (← CellStore.read c) with
      | .rat q => return some q
      | _ => return none
    | none => return defQ
  -- Optimistic pass: maybe everything is rational
  let pVars := p.vars
  let mut cache : Array (Var × Rat) := #[]
  let mut allRat := true
  for x in pVars do
    match (← readQ x) with
    | some q => cache := cache.push (x, q)
    | none => allRat := false; break
  if allRat then
    let v := p.evalRat fun x =>
      match cache.foldl (fun acc (y, q) => if y == x then some q else acc) none with
      | some q => q
      | none => defQ.getD 0
    return signOfInt (if v < 0 then -1 else if v == 0 then 0 else 1)
  -- Eliminate the rational fragment
  let mut p' := p
  for x in pVars do
    match (← readQ x) with
    | some q => p' := p'.substRat x q
    | _ => pure ()
  if p'.isZero then
    return 0
  if let some c := p'.asConst? then
    return signOfInt c
  let xs := p'.vars
  let cellI := fun (ivs : Array (Var × MpbqI)) (x : Var) =>
    match ivs.foldl (fun acc (y, i) => if y == x then some i else acc) none with
    | some i => i
    | none => ⟨Mpbq.ofInt 0, Mpbq.ofInt 0⟩   -- unreachable: rationals substituted
  let readIntervals : CellM (Array (Var × MpbqI)) := do
    let mut ivs : Array (Var × MpbqI) := #[]
    for x in xs do
      match (← CellStore.read (σ.get? x).get!) with
      | .root _ a b _ => ivs := ivs.push (x, ⟨a, b⟩)
      | _ => pure ()
    return ivs
  -- Restartable main loop (z3 while(true) with became-basic restart)
  let mut restart := true
  let mut result : Int := 0
  while restart do
    restart := false
    -- Interval pass: refine (magnitude-gated) while the enclosure straddles 0
    let mut ri := p'.evalInterval (cellI (← readIntervals))
    let mut phaseDone := false
    while !phaseDone && !restart do
      if !ri.containsZero then
        result := (if ri.isPos then 1 else -1)
        phaseDone := true
      else
        let mut anyRefined := false
        for x in xs do
          let c := (σ.get? x).get!
          let v ← CellStore.read c
          if RAlg.magnitude v > RAlg.minMagnitude then
            CellStore.refine1C c
            match (← CellStore.read c) with
            | .rat _ => restart := true   -- became basic: restart all
            | _ => anyRefined := true
        if !anyRefined && !restart then
          phaseDone := true
        else if !restart then
          ri := p'.evalInterval (cellI (← readIntervals))
    -- Exact zero test via resultants
    if !restart && !phaseDone then
      let y := (xs.foldl (fun acc x => max acc x) 0) + 1
      let xsSorted ← sortByValueDegree σ xs
      let mut bigR := MPoly.sub (MPoly.ofVar y) p'
      for x in xsSorted do
        match (← CellStore.read (σ.get? x).get!) with
        | .root qp _ _ _ => bigR := resultantElim bigR x qp
        | _ => pure ()
      let k := match bigR.toQPoly? y with
        | some qR => nonzeroRootLowerBound qR
        | none => 0   -- unreachable: R is univariate in y
      let lM : Mpbq := Mpbq.mk (-1) k
      let uM : Mpbq := Mpbq.mk 1 k
      let inRange := fun (i : MpbqI) => Mpbq.lt lM i.lo && Mpbq.lt i.hi uM
      if inRange ri then
        result := 0
        phaseDone := true
      else
        -- save the cells (z3 save_intervals) before the final loop
        let mut saved : Array (Var × CellId × RAlg) := #[]
        for x in xs do
          let c := (σ.get? x).get!
          saved := saved.push (x, c, ← CellStore.read c)
        let mut finalDone := false
        while !finalDone && !restart do
          ri := p'.evalInterval (cellI (← readIntervals))
          if !ri.containsZero then
            result := (if ri.isPos then 1 else -1)
            finalDone := true
          else if inRange ri then
            result := 0
            finalDone := true
          else
            for x in xs do
              let c := (σ.get? x).get!
              CellStore.refine1C c
              match (← CellStore.read c) with
              | .rat _ => restart := true
              | _ => pure ()
        -- restore_if_too_small (on every exit of the resultant phase)
        for (_, c, sv) in saved do
          match (← CellStore.read c) with
          | v@(.root _ _ _ _) =>
            if RAlg.magnitude v < RAlg.minMagnitude then
              CellStore.write c sv
          | _ => pure ()
  return result

/-- Max variable `< x` appearing in `terms[start..termEnd)` (z3
`polynomial::max_smaller_than`). -/
private def maxSmallerThan (terms : Array (Int × Monomial)) (start termEnd : Nat)
    (x : Var) : Option Var := Id.run do
  let mut best : Option Var := none
  for i in [start:termEnd] do
    for (y, _) in terms[i]!.2 do
      if y < x then
        match best with
        | none => best := some y
        | some b => if b < y then best := some y
  return best

/-- z3 `t_eval_core` (polynomial.cpp:6676): evaluate the sub-polynomial
of monomials `[start, termEnd)` over variables `≤ x` with op-by-op anum
arithmetic — Horner over `x` with recursive coefficient evaluation.
Stored cells are refined through the ops (z3 reaches them via the
public const_cast wrappers); temps are overwritten per op call in both
worlds, so no temp threading is needed. Precondition (z3 SASSERT):
every variable `≤ x` in the slice is assigned. -/
partial def evalCore (terms : Array (Int × Monomial)) (σ : Assignment)
    (start termEnd : Nat) (x : Var) : CellM RAlg := do
  if termEnd == start + 1 then
    let (a, m) := terms[start]!
    let mut r : RAlg := .rat a
    for (y, d) in m do
      if y > x then break
      let cy := (σ.get? y).get!    -- z3 SASSERT(x2v.contains(y))
      let (pw, vy') := RAlg.power (← CellStore.read cy) d
      CellStore.write cy vy'
      r := (RAlg.mul r pw).1
    return r
  else
    let cx := (σ.get? x).get!      -- z3 SASSERT(x2v.contains(x))
    let mut r : RAlg := .rat 0
    let mut i := start
    while i < termEnd do
      let d := terms[i]!.2.degreeIn x
      if d == 0 then
        match maxSmallerThan terms i termEnd x with
        | none => r := (RAlg.add r (.rat terms[i]!.1)).1
        | some y => r := (RAlg.add r (← evalCore terms σ i termEnd y)).1
        break
      let mut j := i + 1
      let mut nextD := 0
      while j < termEnd do
        let dj := terms[j]!.2.degreeIn x
        if dj < d then
          nextD := dj
          break
        j := j + 1
      let aux ← match maxSmallerThan terms i j x with
        | none => pure (.rat terms[i]!.1)
        | some y => evalCore terms σ i j y
      r := (RAlg.add r aux).1
      let (pw, xv') := RAlg.power (← CellStore.read cx) (d - nextD)
      CellStore.write cx xv'
      r := (RAlg.mul r pw).1
      i := j
    return r

/-- z3 `imp::eval` = `t_eval` (polynomial.cpp:6749/6793): evaluate `p`
at the assignment with op-by-op anum arithmetic. z3 lex-sorts first;
our MPoly is already canonical (the approved eager-sorted
representation). Precondition (z3 SASSERT): every variable of `p` is
assigned. -/
partial def evalAnum (p : MPoly) (σ : Assignment) : CellM RAlg := do
  if p.isZero then return .rat 0
  if let some c := p.asConst? then return .rat c
  let x := p.maxVar.getD 0
  evalCore p.toArray σ 0 p.length x

/-- z3 `isolate_roots` under partial assignment (`algebraic_numbers.cpp:2547`).
Roots are fresh store cells. The `q ≡ 0` degenerate fallbacks
(:2622-2699) are ported: linear-coefficient solve via anum division,
and the auxiliary-z nested elimination. `nested` is the recursive-call
flag — the fallback is unreachable under it (z3 `SASSERT(!nested_call)`;
the nested resultant cannot vanish since 0 is not a root of the
polynomial defining the auxiliary value) and returns `none` there.
`partial`: z3's recursion is capped at one nesting level by the flag —
not structural for Lean. -/
partial def isolateRootsAt (p : MPoly) (σ : Assignment) (nested : Bool := false) :
    CellM (Option (Array CellId)) := do
  let freshAll (rs : Array RAlg) : CellM (Array CellId) := do
    let mut out : Array CellId := #[]
    for r in rs do
      out := out.push (← CellStore.fresh r)
    return out
  if p.isZero || p.asConst?.isSome then
    return some #[]
  -- univariate shortcut: isolate directly in its only variable
  if p.vars.size == 1 then
    let x := p.vars[0]!
    match p.toQPoly? x with
    | some q => return some (← freshAll (RAlg.isolateRoots q))
    | none => return some #[]   -- unreachable
  -- eliminate the rational fragment
  let mut p' := p
  for x in p.vars do
    match σ.get? x with
    | some c =>
      match (← CellStore.read c) with
      | .rat q => p' := p'.substRat x q
      | _ => pure ()
    | none => pure ()
  if p'.isZero || p'.asConst?.isSome then
    return some #[]
  if p'.vars.size == 1 then
    let x := p'.vars[0]!
    if σ.contains x then
      -- the unassigned variable vanished under substitution: no roots
      return some #[]
    match p'.toQPoly? x with
    | some q => return some (← freshAll (RAlg.isolateRoots q))
    | none => return some #[]   -- unreachable
  -- sort variables by the degree of the values; the target is last
  let xs ← sortByValueDegree σ p'.vars
  let x := xs.back!
  if σ.contains x then
    return some #[]
  -- resultant-eliminate every assigned algebraic variable
  let mut q := p'
  for y in xs[:xs.size - 1] do
    if !q.isZero then
      match (← CellStore.read (σ.get? y).get!) with
      | .root qp _ _ _ => q := resultantElim q y qp
      | _ => pure ()
  if q.isZero then
    if nested then
      -- z3 SASSERT(!nested_call): unreachable — the nested resultant
      -- cannot vanish (0 is not a root of the poly defining `a`)
      return none
    -- q ≡ 0 degenerate fallback (:2628-2699)
    let n := p'.degreeIn x
    if n == 1 then
      -- p' is linear in x: evaluate the coefficients; root = −a0/a1
      let cs := p'.coeffsIn x
      let a0 ← evalAnum (cs.getD 0 []) σ
      let a1 ← evalAnum (cs.getD 1 []) σ
      if RAlg.isZeroV a1 then
        -- coefficient of degree 1 vanished: p' has no roots at σ
        return some #[]
      let (d, _, _) := RAlg.div a0 a1
      return some #[← CellStore.fresh (RAlg.neg d)]
    -- scan coefficients i = n … 1 for the first non-vanishing one
    let cs := p'.coeffsIn x
    let mut i := n
    let mut a : RAlg := .rat 0
    while i ≥ 1 do
      a ← evalAnum (cs.getD i []) σ
      if !RAlg.isZeroV a then break
      i := i - 1
    if i == 0 then
      -- all coefficients of x vanished: p' has no roots at σ
      return some #[]
    -- auxiliary variable: q2 = z·xⁱ + (p' with x-degree capped at i−1),
    -- isolate with σ extended by z ↦ a (z3 ext_var2num)
    let z := (p'.maxVar.getD 0) + 1
    let trunc : MPoly := p'.filter fun (_, m) => m.degreeIn x ≤ i - 1
    let zxi : MPoly := [(1, [(x, i), (z, 1)])]   -- var-ascending (z > x)
    let q2 := MPoly.add zxi trunc
    let zc ← CellStore.fresh a
    return (← isolateRootsAt q2 (σ.set z zc) true)
  if q.asConst?.isSome then
    return some #[]
  -- isolate the univariate q and filter candidates by exact sign
  match q.toQPoly? x with
  | none => return some #[]   -- unreachable: q is univariate in x
  | some qq =>
    let mut kept : Array CellId := #[]
    for r in RAlg.isolateRoots qq do
      let c ← CellStore.fresh r
      let s ← evalSignAt p' (σ.set x c)
      if s == 0 then
        kept := kept.push c
    return some kept

/-- z3's `DEFAULT_PRECISION` (`algebraic_numbers.cpp:2900`). -/
def defaultPrecision : Nat := 2

/-- The signs variant (`algebraic_numbers.cpp:2902`): roots of `p` under
`σ` plus the sign of `p` on every cell they cut the line into —
`numRoots + 1` signs (or a single sign when there are no roots).
Samples: `intLt` below, `select` between, `intGt` above; every
unassigned variable takes the sample (z3 `ext2_var2num`). -/
def isolateRootsSigns (p : MPoly) (σ : Assignment) :
    CellM (Option (Array CellId × Array Int)) := do
  match (← isolateRootsAt p σ) with
  | none => return none
  | some roots =>
    if roots.isEmpty then
      let s ← evalSignAt p σ (some 0)
      return some (#[], #[s])
    for i in [:roots.size] do
      CellStore.refineUntilPrecC roots[i]! defaultPrecision
    let mut signs : Array Int := #[]
    let lo ← CellStore.intLtC roots[0]!
    signs := signs.push (← evalSignAt p σ (some (mkRat lo 1)))
    for i in [1:roots.size] do
      let w ← CellStore.selectC roots[i - 1]! roots[i]!
      signs := signs.push (← evalSignAt p σ (some w))
    let hi ← CellStore.intGtC roots[roots.size - 1]!
    signs := signs.push (← evalSignAt p σ (some (mkRat hi 1)))
    return some (roots, signs)

end AnumEval

end LeanNonlinearArith.Nlsat
