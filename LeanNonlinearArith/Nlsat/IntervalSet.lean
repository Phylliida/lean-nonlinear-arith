import LeanNonlinearArith.Kernel.CellStore
import LeanNonlinearArith.Nlsat.Types

/-!
# nla-12a — infeasible interval sets (port of `nlsat_interval_set.cpp`)

Sets of disjoint intervals with algebraic endpoints, each carrying the
literal that justifies its infeasibility (plus an optional clause id).
The solver tracks, per arithmetic variable, the union of intervals its
watched literals rule out; a full set = conflict, otherwise
`pickInComplement` produces the next sample point.

**Cell-store model (2026-07-28, see `Kernel/CellStore.lean`):** interval
endpoints are `CellId`s into the store. z3's owner-level sharing —
`int_gt`/`int_lt` `const_cast` refinement of *stored* endpoints,
`select`/`lt` refining endpoints they compare, witnesses that ARE a
shared endpoint cell — is structural: operations run in `CellM` and
refinement happens in place, visible to every holder of the id. The
nla-28 tuple threading this replaces is gone from this layer; the pure
`RAlg` ops it built on are unchanged underneath.

Fidelity notes (source: `nlsat_interval_set.cpp`, case comments kept):

* `mkUnion` is the exact nine-case sweep, including which side's
  justification survives on splits — conflict-lemma minimality depends
  on this, so the cases are transcribed 1:1 rather than re-derived.
* Compression merges *adjacent* intervals only when their justifications
  coincide (Z3 remark: "we only combine adjacent intervals when they
  have the same justification").
* `pickInComplement` keeps Z3's deterministic (randomize=false)
  preference order: zero, an integer above everything, an integer below
  everything, a rational in some gap, a shared *rational* open endpoint,
  and finally an irrational shared endpoint as the witness. Since
  nla-26.4 the selection entry points are the actual `am` ports
  (`intGt`/`intLt`/`select` with dyadic `select_small_core` niceness),
  and the shared-endpoint scan goes through `is_rational` exactly as
  z3's does (root-represented rationals are discovered, nla-28).
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-- One infeasible interval. Endpoints are store cells (`CellId`); the
`Inf` flags make the corresponding endpoint meaningless (infinite ends
are always open). Invariants (`check_interval`): `lowerInf → lowerOpen`,
`upperInf → upperOpen`, and `lower ≤ upper` with equality only when both
ends are closed (singleton). -/
structure NInterval where
  lowerOpen : Bool
  lowerInf : Bool
  lower : CellId
  upperOpen : Bool
  upperInf : Bool
  upper : CellId
  just : Literal
  clauseId : Option Nat
deriving Repr, Inhabited, BEq

/-- Nonempty interval set: sorted, disjoint intervals; `full` caches
"covers ℝ". Z3's empty set is the null pointer — ours is `none` at the
`IntervalSet` level. -/
structure IntervalSetData where
  intervals : Array NInterval
  full : Bool
deriving Repr, Inhabited, BEq

abbrev IntervalSet := Option IntervalSetData

namespace IntervalSet

/-- Singleton-interval set from fresh endpoint VALUES (`interval_set_manager::mk`
with fresh cells — the test/direct-construction path). -/
def mk (lowerOpen lowerInf : Bool) (lower : RAlg)
    (upperOpen upperInf : Bool) (upper : RAlg)
    (just : Literal) (clauseId : Option Nat := none) : CellM IntervalSet := do
  let lo ← CellStore.fresh lower
  let hi ← CellStore.fresh upper
  return some {
    intervals := #[{
      lowerOpen := lowerOpen || lowerInf, lowerInf, lower := lo
      upperOpen := upperOpen || upperInf, upperInf, upper := hi
      just, clauseId }]
    full := lowerInf && upperInf }

/-- Singleton-interval set from existing endpoint CELLS (`mk` sharing
the cells — z3's `m_am.set` shares the underlying cell object; this is
the evaluator path, where endpoints are sign-table sections). -/
def mkIds (lowerOpen lowerInf : Bool) (lower : CellId)
    (upperOpen upperInf : Bool) (upper : CellId)
    (just : Literal) (clauseId : Option Nat := none) : IntervalSet :=
  some {
    intervals := #[{
      lowerOpen := lowerOpen || lowerInf, lowerInf, lower
      upperOpen := upperOpen || upperInf, upperInf, upper
      just, clauseId }]
    full := lowerInf && upperInf }

def isEmpty (s : IntervalSet) : Bool := s.isNone

def isFull (s : IntervalSet) : Bool :=
  match s with
  | none => false
  | some d => d.full

def numIntervals (s : IntervalSet) : Nat :=
  match s with
  | none => 0
  | some d => d.intervals.size

/-! ## Endpoint comparisons (`compare_lower_lower` etc.)

Refinements from the compares persist in the store (z3's shared-cell
mutation); the interval structures themselves are unchanged — endpoint
ids are stable. -/

def cmpLowerLower (i1 i2 : NInterval) : CellM Ordering := do
  if i1.lowerInf && i2.lowerInf then return .eq
  else if i1.lowerInf then return .lt
  else if i2.lowerInf then return .gt
  else
    match (← CellStore.compareC i1.lower i2.lower) with
    | .eq =>
      if i1.lowerOpen == i2.lowerOpen then return .eq
      else if i1.lowerOpen then return .gt
      else return .lt
    | o => return o

def cmpUpperUpper (i1 i2 : NInterval) : CellM Ordering := do
  if i1.upperInf && i2.upperInf then return .eq
  else if i1.upperInf then return .gt
  else if i2.upperInf then return .lt
  else
    match (← CellStore.compareC i1.upper i2.upper) with
    | .eq =>
      if i1.upperOpen == i2.upperOpen then return .eq
      else if i1.upperOpen then return .lt
      else return .gt
    | o => return o

/-- `i1.upper` versus `i2.lower` — the disjointness comparison; `.eq`
means the closed endpoints touch. -/
def cmpUpperLower (i1 i2 : NInterval) : CellM Ordering := do
  if i1.upperInf || i2.lowerInf then return .gt
  else
    match (← CellStore.compareC i1.upper i2.lower) with
    | .eq => return (if !i1.upperOpen && !i2.lowerOpen then .eq else .lt)
    | o => return o

/-- No space between `curr` and `next` (`adjacent`): endpoint values
equal and at least one side closed. -/
def adjacent (curr next : NInterval) : CellM Bool := do
  if curr.upperInf || next.lowerInf then return false
  else
    match (← CellStore.compareC curr.upper next.lower) with
    | .eq => return (!curr.upperOpen || !next.lowerOpen)
    | _ => return false

/-! ## Union -/

/-- The `mk_union` sweep. Case structure and justification choices are
transcribed 1:1 from `nlsat_interval_set.cpp` (comments preserved).
Endpoint compares during the sweep refine the stored cells in place —
visible to every owner, exactly z3. -/
def mkUnion (s1 s2 : IntervalSet) : CellM IntervalSet := do
  match s1, s2 with
  | none, _ => return s2
  | _, none => return s1
  | some d1, some d2 =>
    if d1 == d2 then return s2
    if d1.full then return s1
    if d2.full then return s2
    let ints1 := d1.intervals
    let ints2 := d2.intervals
    let mut result : Array NInterval := #[]
    let mut i1 : Nat := 0
    let mut i2 : Nat := 0
    while i1 < ints1.size || i2 < ints2.size do
      if i1 >= ints1.size then
        result := result.push ints2[i2]!
        i2 := i2 + 1
      else if i2 >= ints2.size then
        result := result.push ints1[i1]!
        i1 := i1 + 1
      else
        let int1 := ints1[i1]!
        let int2 := ints2[i2]!
        let l1l2 ← cmpLowerLower int1 int2
        let u1u2 ← cmpUpperUpper int1 int2
        if l1l2 != .gt then
          if u1u2 == .eq then
            -- 1)  [     ]      2) [     ]
            --     [     ]           [   ]
            result := result.push int1
            i1 := i1 + 1
            i2 := i2 + 1
          else if u1u2 == .gt then
            -- 1) [        ]    2) [        ]
            --    [     ]            [   ]
            i2 := i2 + 1  -- i1 may consume other intervals of s2
          else
            let u1l2 ← cmpUpperLower int1 int2
            if u1l2 == .lt then
              -- 1)   [      ]
              --                 [     ]
              result := result.push int1
              i1 := i1 + 1
            else if u1l2 == .eq then
              -- touching closed endpoints
              if l1l2 != .eq then
                -- 1)   [   ]
                --          [    ]
                result := result.push { int1 with
                  upperOpen := true, upperInf := false }
                i1 := i1 + 1
              else
                -- 2)   u          <<< int1 is a singleton
                --      [     ]
                i1 := i1 + 1  -- just consume int1
            else
              if l1l2 == .eq then
                -- 1)   [      ]
                --      [          ]
                i1 := i1 + 1  -- just consume int1
              else
                -- 2) [        ]
                --         [        ]
                result := result.push { int1 with
                  upperOpen := !int2.lowerOpen, upperInf := false,
                  upper := int2.lower }
                i1 := i1 + 1
        else
          if u1u2 == .eq then
            -- 1)    [  ]
            --    [     ]
            result := result.push int2
            i1 := i1 + 1
            i2 := i2 + 1
          else if u1u2 == .lt then
            -- 1)   [   ]
            --    [       ]
            i1 := i1 + 1  -- i2 may consume other intervals of s1
          else
            let u2l1 ← cmpUpperLower int2 int1
            if u2l1 == .lt then
              -- 1)           [      ]
              --     [     ]
              result := result.push int2
              i2 := i2 + 1
            else if u2l1 == .eq then
              --      [    ]
              --  [   ]
              result := result.push { int2 with
                upperOpen := true, upperInf := false }
              i2 := i2 + 1
            else
              --     [        ]
              -- [        ]
              result := result.push { int2 with
                upperOpen := !int1.lowerOpen, upperInf := false,
                upper := int1.lower }
              i2 := i2 + 1
    -- Compress: only combine adjacent intervals with the SAME justification
    let mut compressed : Array NInterval := #[]
    for iv in result do
      if compressed.isEmpty then
        compressed := compressed.push iv
      else
        let last := compressed.back!
        if last.just == iv.just && (← adjacent last iv) then
          compressed := compressed.set! (compressed.size - 1) { last with
            upperOpen := iv.upperOpen, upperInf := iv.upperInf,
            upper := iv.upper }
        else
          compressed := compressed.push iv
    -- Full iff no slack at the ends and no gap between neighbors
    let sz := compressed.size
    let mut foundSlack :=
      !compressed[0]!.lowerInf || !compressed[sz - 1]!.upperInf
    for i in [1:sz] do
      if !foundSlack then
        if !(← adjacent compressed[i-1]! compressed[i]!) then
          foundSlack := true
    return some { intervals := compressed, full := !foundSlack }

/-! ## Justifications -/

/-- Distinct justification literals (and clause ids) of a set
(`get_justifications`). -/
def justifications (s : IntervalSet) : Array Literal × Array Nat := Id.run do
  let mut lits : Array Literal := #[]
  let mut cls : Array Nat := #[]
  match s with
  | none => return (lits, cls)
  | some d =>
    for iv in d.intervals do
      if !lits.contains iv.just then
        lits := lits.push iv.just
        if let some cid := iv.clauseId then
          if !cls.contains cid then
            cls := cls.push cid
    return (lits, cls)

/-! ## Witness selection (`pick_in_complement`, deterministic path) -/

/-- Position of zero relative to an interval: `-1` if the interval is
entirely below 0, `1` if entirely above, `0` if it contains 0
(`compare_interval_with_zero`). The compares are root-vs-rational,
which never refines, so no write-back is needed. -/
def cmpWithZero (iv : NInterval) : CellM Int := do
  if !iv.upperInf then
    let u ← CellStore.read iv.upper
    match (RAlg.compare u (.rat 0)).1 with
    | .lt => return -1
    | .eq => if iv.upperOpen then return -1
    | _ => pure ()
  if !iv.lowerInf then
    let l ← CellStore.read iv.lower
    match (RAlg.compare l (.rat 0)).1 with
    | .gt => return 1
    | .eq => if iv.lowerOpen then return 1
    | _ => pure ()
  return 0

/-- Pick a witness in the complement (Z3 preference order,
randomize = false), as a store cell: `none` only for a full set.
z3 `pick_in_complement(interval_set const *, ..., anum & w, ...)` sets
`w` — for a shared-endpoint witness, to the endpoint cell ITSELF (we
return that cell's id, sharing it exactly as z3's `m_am.set` does). -/
def pickInComplement (s : IntervalSet) : CellM (Option CellId) := do
  match s with
  | none => CellStore.fresh (.rat 0)
  | some d =>
    if d.full then return none
    let ints := d.intervals
    let num := ints.size
    -- try zero first, to keep polynomials simple
    let mut zeroOk := true
    for iv in ints do
      let sgn ← cmpWithZero iv
      if sgn == 0 then
        zeroOk := false
        break
      else if sgn > 0 then
        break
    if zeroOk then CellStore.fresh (.rat 0)
    -- an integer above everything
    else if !ints[num - 1]!.upperInf then
      let n ← CellStore.intGtC ints[num - 1]!.upper
      CellStore.fresh (.rat (mkRat n 1))
    -- an integer below everything
    else if !ints[0]!.lowerInf then
      let n ← CellStore.intLtC ints[0]!.lower
      CellStore.fresh (.rat (mkRat n 1))
    else
      -- a "nice" dyadic rational inside some non-unit gap
      let mut witness : Option CellId := none
      for i in [1:num] do
        if witness.isNone then
          if (← CellStore.ltC ints[i-1]!.upper ints[i]!.lower) then
            let w ← CellStore.selectC ints[i-1]!.upper ints[i]!.lower
            witness := some (← CellStore.fresh (.rat w))
      match witness with
      | some _ => return witness
      | none =>
        -- shared open endpoints: prefer a rational one (z3 `is_rational`
        -- discovers rationals in root representation and converts them)
        let mut irrational : Option CellId := none
        for i in [1:num] do
          if witness.isNone then
            if ints[i-1]!.upperOpen && ints[i]!.lowerOpen then
              if (← CellStore.isRationalC ints[i-1]!.upper) then
                witness := some ints[i-1]!.upper
              else if irrational.isNone then
                irrational := some ints[i-1]!.upper
        match witness with
        | some _ => return witness
        | none => return irrational

end IntervalSet

end LeanNonlinearArith.Nlsat
