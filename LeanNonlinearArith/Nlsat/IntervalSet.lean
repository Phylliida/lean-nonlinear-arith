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
  and finally an irrational shared endpoint as the witness. Since
  nla-26.4 the selection entry points are the actual `am` ports
  (`intGt`/`intLt`/`select` with dyadic `select_small_core` niceness).
* nla-28 (statefulness threading): z3's `pick_in_complement` and the
  `mk_union` sweep refine the STORED endpoint cells as a side effect
  (`int_gt`/`int_lt` const_cast, `lt`/`select`/`compare` take
  `numeral &`, `is_rational` can convert a cell to basic). The ports
  return the refined sets/intervals alongside their results — the
  persistent-structure image of z3's shared-cell mutation — and the
  solver store (12c) will own the threading. The shared-endpoint
  rational preference now goes through the `is_rational` port exactly as
  z3's does, so a root-represented rational endpoint is DISCOVERED
  (rational-root theorem) and returned as `.rat` — the former
  root-represented-rational divergence at this spot is dissolved.
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

/-! ## Endpoint comparisons (`compare_lower_lower` etc.)

nla-28: z3's `m_am.compare` mutates both endpoints (refinement persists
in the stored sets — the cells are shared), so each comparison returns
the refined intervals alongside the verdict. Callers thread them back
into the arrays the intervals came from. -/

def cmpLowerLower (i1 i2 : NInterval) : Ordering × NInterval × NInterval :=
  if i1.lowerInf && i2.lowerInf then (.eq, i1, i2)
  else if i1.lowerInf then (.lt, i1, i2)
  else if i2.lowerInf then (.gt, i1, i2)
  else match RAlg.compare i1.lower i2.lower with
    | (.eq, l1, l2) =>
      if i1.lowerOpen == i2.lowerOpen then (.eq, { i1 with lower := l1 }, { i2 with lower := l2 })
      else if i1.lowerOpen then (.gt, { i1 with lower := l1 }, { i2 with lower := l2 })
      else (.lt, { i1 with lower := l1 }, { i2 with lower := l2 })
    | (o, l1, l2) => (o, { i1 with lower := l1 }, { i2 with lower := l2 })

def cmpUpperUpper (i1 i2 : NInterval) : Ordering × NInterval × NInterval :=
  if i1.upperInf && i2.upperInf then (.eq, i1, i2)
  else if i1.upperInf then (.gt, i1, i2)
  else if i2.upperInf then (.lt, i1, i2)
  else match RAlg.compare i1.upper i2.upper with
    | (.eq, u1, u2) =>
      if i1.upperOpen == i2.upperOpen then (.eq, { i1 with upper := u1 }, { i2 with upper := u2 })
      else if i1.upperOpen then (.lt, { i1 with upper := u1 }, { i2 with upper := u2 })
      else (.gt, { i1 with upper := u1 }, { i2 with upper := u2 })
    | (o, u1, u2) => (o, { i1 with upper := u1 }, { i2 with upper := u2 })

/-- `i1.upper` versus `i2.lower` — the disjointness comparison; `.eq`
means the closed endpoints touch. -/
def cmpUpperLower (i1 i2 : NInterval) : Ordering × NInterval × NInterval :=
  if i1.upperInf || i2.lowerInf then (.gt, i1, i2)
  else match RAlg.compare i1.upper i2.lower with
    | (.eq, u, l) =>
      (if !i1.upperOpen && !i2.lowerOpen then .eq else .lt,
       { i1 with upper := u }, { i2 with lower := l })
    | (o, u, l) => (o, { i1 with upper := u }, { i2 with lower := l })

/-- No space between `curr` and `next` (`adjacent`): endpoint values
equal and at least one side closed. -/
def adjacent (curr next : NInterval) : Bool × NInterval × NInterval :=
  if curr.upperInf || next.lowerInf then (false, curr, next)
  else match RAlg.compare curr.upper next.lower with
    | (.eq, u, l) => (!curr.upperOpen || !next.lowerOpen,
                      { curr with upper := u }, { next with lower := l })
    | (_, u, l) => (false, { curr with upper := u }, { next with lower := l })

/-! ## Union -/

/-- The `mk_union` sweep. Case structure and justification choices are
transcribed 1:1 from `nlsat_interval_set.cpp` (comments preserved).
nla-28: z3's endpoint compares during the sweep refine the STORED input
sets in place (shared cells); we return the refined `s1`/`s2` alongside
the union — `(s1', s2', union)` — and refined endpoints also flow into
the union's intervals. -/
def mkUnion (s1 s2 : IntervalSet) : IntervalSet × IntervalSet × IntervalSet := Id.run do
  match s1, s2 with
  | none, _ => return (s1, s2, s2)
  | _, none => return (s1, s2, s1)
  | some d1, some d2 =>
    if d1 == d2 then return (s1, s2, s2)
    if d1.full then return (s1, s2, s1)
    if d2.full then return (s1, s2, s2)
    let mut ints1 := d1.intervals
    let mut ints2 := d2.intervals
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
        let (l1l2, int1a, int2a) := cmpLowerLower ints1[i1]! ints2[i2]!
        let (u1u2, int1, int2) := cmpUpperUpper int1a int2a
        ints1 := ints1.set! i1 int1
        ints2 := ints2.set! i2 int2
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
            let (u1l2, int1', int2') := cmpUpperLower int1 int2
            ints1 := ints1.set! i1 int1'
            ints2 := ints2.set! i2 int2'
            if u1l2 == .lt then
              -- 1)   [      ]
              --                 [     ]
              result := result.push int1'
              i1 := i1 + 1
            else if u1l2 == .eq then
              -- touching closed endpoints
              if l1l2 != .eq then
                -- 1)   [   ]
                --          [    ]
                result := result.push { int1' with
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
                result := result.push { int1' with
                  upperOpen := !int2'.lowerOpen, upperInf := false,
                  upper := int2'.lower }
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
            let (u2l1, int2', int1') := cmpUpperLower int2 int1
            ints1 := ints1.set! i1 int1'
            ints2 := ints2.set! i2 int2'
            if u2l1 == .lt then
              -- 1)           [      ]
              --     [     ]
              result := result.push int2'
              i2 := i2 + 1
            else if u2l1 == .eq then
              --      [    ]
              --  [   ]
              result := result.push { int2' with
                upperOpen := true, upperInf := false }
              i2 := i2 + 1
            else
              --     [        ]
              -- [        ]
              result := result.push { int2' with
                upperOpen := !int1'.lowerOpen, upperInf := false,
                upper := int1'.lower }
              i2 := i2 + 1
    -- Compress: only combine adjacent intervals with the SAME justification
    let mut compressed : Array NInterval := #[]
    for iv in result do
      if compressed.isEmpty then
        compressed := compressed.push iv
      else
        let last := compressed.back!
        let (adj, last', iv') := adjacent last iv
        if last'.just == iv'.just && adj then
          compressed := compressed.set! (compressed.size - 1) { last' with
            upperOpen := iv'.upperOpen, upperInf := iv'.upperInf,
            upper := iv'.upper }
        else
          compressed := (compressed.set! (compressed.size - 1) last').push iv'
    -- Full iff no slack at the ends and no gap between neighbors
    let sz := compressed.size
    let mut foundSlack :=
      !compressed[0]!.lowerInf || !compressed[sz - 1]!.upperInf
    for i in [1:sz] do
      if !foundSlack then
        let (adj, prev', curr') := adjacent compressed[i-1]! compressed[i]!
        compressed := (compressed.set! (i-1) prev').set! i curr'
        if !adj then
          foundSlack := true
    return (some { d1 with intervals := ints1 }, some { d2 with intervals := ints2 },
            some { intervals := compressed, full := !foundSlack })

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
(`compare_interval_with_zero`). Pure: the compares are always
root-vs-rational, which never refines (z3 `compare(algebraic_cell,
mpq)` is mutation-free), so the nla-28 refined cells are the inputs. -/
def cmpWithZero (iv : NInterval) : Int := Id.run do
  if !iv.upperInf then
    match (RAlg.compare iv.upper (.rat 0)).1 with
    | .lt => return -1
    | .eq => if iv.upperOpen then return -1
    | _ => pure ()
  if !iv.lowerInf then
    match (RAlg.compare iv.lower (.rat 0)).1 with
    | .gt => return 1
    | .eq => if iv.lowerOpen then return 1
    | _ => pure ()
  return 0

/-- Pick a witness in the complement (Z3 preference order,
randomize = false). Returns `(none, s')` only for a full set. nla-26.4:
the three selection entry points are the actual `am` ports —
`intGt`/`intLt` (refine-then-floor/ceil) and `select` (separate + dyadic
`select_small_core` smallest-denominator gap witnesses). nla-28: z3
refines the STORED endpoints through every one of these calls
(`int_gt`/`int_lt` const_cast, `lt`/`select` take `numeral &`,
`is_rational` refines and can convert to basic); we return the set with
refined endpoints threaded back alongside the witness. The shared
open-endpoint scan now calls the `is_rational` port (as z3 does), which
discovers rational values in root representation — the old
root-represented-rational divergence at this spot is dissolved. -/
def pickInComplement (s : IntervalSet) : Option RAlg × IntervalSet := Id.run do
  match s with
  | none => return (some (.rat 0), none)
  | some d =>
    if d.full then return (none, s)
    let mut ints := d.intervals
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
    if zeroOk then return (some (.rat 0), some { d with intervals := ints })
    -- an integer above everything
    if !ints[num - 1]!.upperInf then
      let (n, u') := RAlg.intGt ints[num - 1]!.upper
      ints := ints.set! (num - 1) { ints[num - 1]! with upper := u' }
      return (some (.rat (n : Int)), some { d with intervals := ints })
    -- an integer below everything
    if !ints[0]!.lowerInf then
      let (n, l') := RAlg.intLt ints[0]!.lower
      ints := ints.set! 0 { ints[0]! with lower := l' }
      return (some (.rat (n : Int)), some { d with intervals := ints })
    -- a "nice" dyadic rational inside some non-unit gap
    for i in [1:num] do
      let u := ints[i-1]!.upper
      let l := ints[i]!.lower
      let (isLt, u', l') := RAlg.lt u l
      ints := (ints.set! (i-1) { ints[i-1]! with upper := u' }).set! i { ints[i]! with lower := l' }
      if isLt then
        let (w, u'', l'') := RAlg.select u' l'
        ints := (ints.set! (i-1) { ints[i-1]! with upper := u'' }).set! i { ints[i]! with lower := l'' }
        return (some (.rat w), some { d with intervals := ints })
    -- shared open endpoints: prefer a rational one (z3 `is_rational`
    -- discovers rationals in root representation and converts them)
    let mut irrational : Option RAlg := none
    for i in [1:num] do
      if ints[i-1]!.upperOpen && ints[i]!.lowerOpen then
        let (isRat, w') := RAlg.isRational ints[i-1]!.upper
        ints := ints.set! (i-1) { ints[i-1]! with upper := w' }
        if isRat then
          return (some w', some { d with intervals := ints })
        if irrational.isNone then irrational := some w'
    -- last option: the irrational shared endpoint
    return (irrational, some { d with intervals := ints })

end IntervalSet

end LeanNonlinearArith.Nlsat
