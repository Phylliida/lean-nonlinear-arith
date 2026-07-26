import LeanNonlinearArith.Kernel.RAlg
import LeanNonlinearArith.Nlsat.Types

/-!
# nla-12a — infeasible interval sets (port of `nlsat_interval_set.cpp`)

Sets of disjoint intervals with algebraic endpoints, each carrying the
literal that justifies its infeasibility (plus an optional clause id).
The solver tracks, per arithmetic variable, the union of intervals its
watched literals rule out; a full set = conflict, otherwise
`pickInComplement` produces the next sample point.

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
  and finally an irrational shared endpoint as the witness.
  Declared minor divergences: Z3's `am.select` prefers "nice" dyadic
  rationals inside gaps (we use `RAlg.ratBetween`'s refinement
  endpoints — same spirit, not bit-identical), and a `root`-represented
  value that happens to be rational (e.g. the root of `x²−4` in
  `(1,3)`) is treated as irrational here because our mini-anum only
  normalizes linear defining polynomials — the witness is still the
  correct number, just in root representation.
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-- One infeasible interval. `lower`/`upper` are meaningless when the
corresponding `Inf` flag is set (infinite ends are always open).
Invariants (`check_interval`): `lowerInf → lowerOpen`,
`upperInf → upperOpen`, and `lower ≤ upper` with equality only when both
ends are closed (singleton). -/
structure NInterval where
  lowerOpen : Bool
  lowerInf : Bool
  lower : RAlg
  upperOpen : Bool
  upperInf : Bool
  upper : RAlg
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

/-- Singleton-interval set (`interval_set_manager::mk`). -/
def mk (lowerOpen lowerInf : Bool) (lower : RAlg)
    (upperOpen upperInf : Bool) (upper : RAlg)
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

/-! ## Endpoint comparisons (`compare_lower_lower` etc.) -/

def cmpLowerLower (i1 i2 : NInterval) : Ordering :=
  if i1.lowerInf && i2.lowerInf then .eq
  else if i1.lowerInf then .lt
  else if i2.lowerInf then .gt
  else match RAlg.compare i1.lower i2.lower with
    | .eq =>
      if i1.lowerOpen == i2.lowerOpen then .eq
      else if i1.lowerOpen then .gt
      else .lt
    | o => o

def cmpUpperUpper (i1 i2 : NInterval) : Ordering :=
  if i1.upperInf && i2.upperInf then .eq
  else if i1.upperInf then .gt
  else if i2.upperInf then .lt
  else match RAlg.compare i1.upper i2.upper with
    | .eq =>
      if i1.upperOpen == i2.upperOpen then .eq
      else if i1.upperOpen then .lt
      else .gt
    | o => o

/-- `i1.upper` versus `i2.lower` — the disjointness comparison; `.eq`
means the closed endpoints touch. -/
def cmpUpperLower (i1 i2 : NInterval) : Ordering :=
  if i1.upperInf || i2.lowerInf then .gt
  else match RAlg.compare i1.upper i2.lower with
    | .eq => if !i1.upperOpen && !i2.lowerOpen then .eq else .lt
    | o => o

/-- No space between `curr` and `next` (`adjacent`): endpoint values
equal and at least one side closed. -/
def adjacent (curr next : NInterval) : Bool :=
  if curr.upperInf || next.lowerInf then false
  else match RAlg.compare curr.upper next.lower with
    | .eq => !curr.upperOpen || !next.lowerOpen
    | _ => false

/-! ## Union -/

/-- The `mk_union` sweep. Case structure and justification choices are
transcribed 1:1 from `nlsat_interval_set.cpp` (comments preserved). -/
def mkUnion (s1 s2 : IntervalSet) : IntervalSet := Id.run do
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
        let l1l2 := cmpLowerLower int1 int2
        let u1u2 := cmpUpperUpper int1 int2
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
            let u1l2 := cmpUpperLower int1 int2
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
            let u2l1 := cmpUpperLower int2 int1
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
        if last.just == iv.just && adjacent last iv then
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
        if !adjacent compressed[i-1]! compressed[i]! then
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
(`compare_interval_with_zero`). -/
def cmpWithZero (iv : NInterval) : Int := Id.run do
  if !iv.upperInf then
    match RAlg.compare iv.upper (.rat 0) with
    | .lt => return -1
    | .eq => if iv.upperOpen then return -1
    | _ => pure ()
  if !iv.lowerInf then
    match RAlg.compare iv.lower (.rat 0) with
    | .gt => return 1
    | .eq => if iv.lowerOpen then return 1
    | _ => pure ()
  return 0

/-- An integer strictly above the value. -/
def intAbove : RAlg → Rat
  | .rat q => (q.floor + 1 : Int)
  | .root _ _ b => (b.floor + 1 : Int)

/-- An integer strictly below the value. -/
def intBelow : RAlg → Rat
  | .rat q => (q.ceil - 1 : Int)
  | .root _ a _ => (a.ceil - 1 : Int)

/-- Pick a witness in the complement (Z3 preference order,
randomize = false). Returns `none` only for a full set. -/
def pickInComplement (s : IntervalSet) : Option RAlg := Id.run do
  match s with
  | none => return some (.rat 0)
  | some d =>
    if d.full then return none
    let ints := d.intervals
    let num := ints.size
    -- try zero first, to keep polynomials simple
    let mut zeroOk := true
    for iv in ints do
      let sgn := cmpWithZero iv
      if sgn == 0 then
        zeroOk := false
        break
      else if sgn > 0 then
        break
    if zeroOk then return some (.rat 0)
    -- an integer above everything
    if !ints[num - 1]!.upperInf then
      return some (.rat (intAbove ints[num - 1]!.upper))
    -- an integer below everything
    if !ints[0]!.lowerInf then
      return some (.rat (intBelow ints[0]!.lower))
    -- a rational inside some non-unit gap
    for i in [1:num] do
      let u := ints[i-1]!.upper
      let l := ints[i]!.lower
      if RAlg.lt u l then
        if let some r := RAlg.ratBetween u l then
          return some (.rat r)
    -- shared open endpoints: prefer a rational one
    let mut irrational : Option RAlg := none
    for i in [1:num] do
      if ints[i-1]!.upperOpen && ints[i]!.lowerOpen then
        match ints[i-1]!.upper with
        | .rat q => return some (.rat q)
        | w => if irrational.isNone then irrational := some w
    -- last option: the irrational shared endpoint
    return irrational

end IntervalSet

end LeanNonlinearArith.Nlsat
