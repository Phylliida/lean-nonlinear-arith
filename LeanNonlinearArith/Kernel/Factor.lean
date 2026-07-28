import LeanNonlinearArith.Kernel.ZPoly

/-!
# nla-27 (slice 2) — factorization over GF(p): square-free decomposition + Berlekamp

Port of the GF(p) half of `upolynomial_factorization.cpp`:

* `zp_square_free_factor` (:251) — Yun's algorithm in characteristic p
  with the Frobenius p-th-root step (Cohen [3] p. 125);
* `berlekamp_matrix` (:61) — the Q−I matrix (row i = x^(p·i) mod f),
  column-operation diagonalization, null-space enumeration;
* `zp_factor_square_free_berlekamp` (:408) with `randomized = false`
  (the deterministic original Berlekamp [1] — what
  `zp_factor_square_free` selects);
* `zp_factor` (:372) — square-free decomposition, then Berlekamp per
  part, multiplicities multiplied through.

Factor sets mirror `zp_factors`: a constant plus `(poly, multiplicity)`
pairs, so `f = constant · ∏ polyᵢ^kᵢ` over GF(p). **Untrusted** (same
trust shape as the rest of `Kernel/`).
-/

namespace LeanNonlinearArith.Kernel

/-- GF(p) factor set (z3 `zp_factors`): `f = constant · ∏ polyᵢ^kᵢ`. -/
structure ZpFactors where
  constant : Int
  factors : Array (Array Int × Nat)
deriving Repr, Inhabited

namespace ZpFactors

def empty : ZpFactors := ⟨1, #[]⟩

def distinct (fs : ZpFactors) : Nat := fs.factors.size

/-- Total factor count with multiplicities (z3 `total_factors`). -/
def total (fs : ZpFactors) : Nat :=
  fs.factors.foldl (fun acc (_, k) => acc + k) 0

/-- Product of all factors with multiplicities, times the constant
(z3 `multiply` + constant) — the reconstructed polynomial. -/
def reconstruct (c : ZpCtx) (fs : ZpFactors) : Array Int :=
  let prod := fs.factors.foldl (fun acc (p, k) =>
    (List.replicate k p).foldl (fun a p => c.pmul a p) acc) #[1]
  c.psmul prod fs.constant

end ZpFactors

/-- z3 `zp_square_free_factor` (:251): square-free decomposition over
GF(p), Cohen [3] p. 125 — Yun's gcd loop with the characteristic-p
Frobenius step (when `T` becomes a p-th power, replace it by its
p-th root and multiply `e` by p). Input `f` need not be monic; the
leading coefficient lands in the constant. -/
def zpSquareFreeFactor (c : ZpCtx) (f : Array Int) : ZpFactors := Id.run do
  let p := c.m.natAbs
  -- T_0 = monic(f); constant = lc(f)
  let f' := c.pnorm f
  let lc := ZpCtx.plc f'
  let constant := lc
  let mut t0 := c.pdivScalarUnit f' lc
  let mut e := 1
  let mut out : Array (Array Int × Nat) := #[]
  while t0.size > 1 do
    let mut k := 0
    let t0d := c.pderivative t0
    let mut t := c.pgcd t0 t0d
    let mut v := c.pdiv t0 t
    while v.size > 1 do
      k := k + 1
      if k % p == 0 then
        k := k + 1
        t := c.pdiv t v
      let w := c.pgcd t v
      let aEk := c.pdiv v w
      v := w
      t := c.pdiv t v
      if aEk.size > 1 then
        out := out.push (aEk, e * k)
    e := e * p
    -- T_0 := p-th root of T: every p-th coefficient
    let mut t0' : Array Int := #[]
    for degP in [0:t.size / p + 1] do
      if degP * p < t.size then
        t0' := t0'.push t[degP * p]!
    t0 := ZpCtx.ptrim t0'
  return ⟨constant, out⟩

/-! ## Berlekamp -/

/-- The Q−I matrix state (z3 `berlekamp_matrix` :61): row `i` is
`x^(p·i) mod f`, stored row-major as an n×n flat array; after
`diagonalize`, `nextNullSpaceVector` enumerates the null-space basis
(skipping the trivial `[1, 0, …, 0]`). -/
structure BerlekampMatrix where
  c : ZpCtx
  mat : Array Int
  size : Nat
  nullRow : Nat
  columnPivot : Array Int   -- -1 = no pivot
  rowPivot : Array Int
deriving Inhabited

namespace BerlekampMatrix

@[inline] def get (m : BerlekampMatrix) (i j : Nat) : Int :=
  m.mat[i * m.size + j]!

@[inline] def set (m : BerlekampMatrix) (i j : Nat) (v : Int) : BerlekampMatrix :=
  { m with mat := m.mat.set! (i * m.size + j) v }

/-- Construction (z3 :88): row 0 = `x⁰ = 1`; each subsequent row `i`
ends up as `x^(p·i)` via the recurrence `a_{k+1,j} = a_{k,j−1} −
a_{k,n−1}·f_j` applied in place (z3 computes every `x^k`, keeping only
every p-th row — the in-place slot update is the same recurrence).
Finishes with Q − I (subtract the identity). -/
def create (c : ZpCtx) (f : Array Int) : BerlekampMatrix := Id.run do
  let n := f.size - 1
  let p := c.m.natAbs
  let mut m : BerlekampMatrix :=
    { c, mat := Array.replicate (n * n) 0, size := n, nullRow := 1
      columnPivot := Array.replicate n (-1), rowPivot := Array.replicate n (-1) }
  m := m.set 0 0 1
  -- x^k in a running slot; every p-th k the slot becomes a matrix row
  let mut slot : Array Int := Array.replicate n 0
  slot := slot.set! 0 1   -- x^0
  let mut row : Nat := 0
  for k in [1:p * (n - 1) + 1] do
    if k % p == 1 then
      row := row + 1
      if row ≥ n then break
      -- slot starts fresh from the previous row's x^(k−1) …
      -- (z3 starts a new row slot here and computes x^k into it from
      -- the previous row, which holds x^(k−1))
      slot := m.mat.extract ((row - 1) * n) (row * n)
    -- slot := slot · x mod f (the recurrence)
    let tmp := slot[n - 1]!
    for j in [:n] do
      let jj := n - 1 - j
      let prev := if jj == 0 then 0 else slot[jj - 1]!
      slot := slot.set! jj (c.sub prev (c.mul tmp (f.getD jj 0)))
    if row < n then
      for j in [:n] do
        m := m.set row j slot[j]!
  -- Q − I
  for i in [:n] do
    m := m.set i i (c.sub (m.get i i) 1)
  return m

/-- Column-operation diagonalization (z3 :158): pivots become −1;
returns the null-space rank (= number of irreducible factors).
Column operations touch rows 1..n−1 only, as in the source. -/
def diagonalize (m : BerlekampMatrix) : BerlekampMatrix × Nat := Id.run do
  let c := m.c
  let n := m.size
  let mut m := m
  let mut nullRank := 0
  for i in [:n] do
    let mut found := false
    for j in [:n] do
      if !found && m.columnPivot[j]! < 0 && m.get i j != 0 then
        found := true
        m := { m with columnPivot := m.columnPivot.set! j (i : Int)
                      rowPivot := m.rowPivot.set! i (j : Int) }
        -- make the pivot −1: multiply column j by −get(i,j)⁻¹
        let mult := c.neg (c.inv (m.get i j))
        for k in [1:n] do
          m := m.set k j (c.mul (m.get k j) mult)
        -- eliminate row i from the other columns
        for oj in [:n] do
          if oj != j then
            let mul2 := m.get i oj
            for k in [1:n] do
              m := m.set k oj (c.addmul mul2 (m.get k j) (m.get k oj))
    if !found then
      nullRank := nullRank + 1
  return (m, nullRank)

/-- Next null-space basis vector (z3 :208), `none` when exhausted.
The trivial `[1, 0, …, 0]` row is skipped (`nullRow` starts at 1). -/
def nextNullSpaceVector (m : BerlekampMatrix) : BerlekampMatrix × Option (Array Int) := Id.run do
  let n := m.size
  let mut m := m
  while m.nullRow < n do
    if m.rowPivot[m.nullRow]! < 0 then
      let r := m.nullRow
      let mut v := Array.replicate n 0
      for j in [:n] do
        if m.rowPivot[j]! ≥ 0 then
          v := v.set! j (m.get r m.rowPivot[j]!.natAbs)
        else if j == r then
          v := v.set! j 1
      m := { m with nullRow := r + 1 }
      return (m, some (ZpCtx.ptrim v))
    m := { m with nullRow := m.nullRow + 1 }
  return (m, none)

end BerlekampMatrix

/-- z3 `zp_factor_square_free_berlekamp` (:408) with `randomized =
false`: factor the monic square-free `f` (deg > 1) over GF(p). Returns
`(factored, factors)` with `factored = false` iff `f` is irreducible
(null-rank 1); `factors` accumulates (the driver appends across calls),
each new factor pushed with multiplicity 1. -/
def zpFactorSquareFreeBerlekamp (c : ZpCtx) (f : Array Int)
    (fs : ZpFactors) : Bool × ZpFactors := Id.run do
  let p := c.m.natAbs
  let qI0 := BerlekampMatrix.create c f
  let firstFactor := fs.distinct
  let mut fs := { fs with factors := fs.factors.push (f, 1) }
  let (qI1, r) := qI0.diagonalize
  if r == 1 then
    return (false, fs)
  let mut qI := qI1
  let mut done := false
  while !done do
    let (qI', vOpt) := qI.nextNullSpaceVector
    qI := qI'
    match vOpt with
    | none => break   -- z3 SASSERTs unreachable
    | some v0 =>
      let mut v := v0
      let currentEnd := fs.distinct
      for ci in [firstFactor:currentEnd] do
        if fs.factors[ci]!.1.size != 2 then
          for _s in [0:p] do
            -- v := v − 1 (the s-loop walks v−1, v−2, …, v−p ≡ v)
            v := v.set! 0 (c.sub (v.getD 0 0) 1)
            let cur := fs.factors[ci]!.1
            let g := c.pgcd v cur
            if g.size != 1 && g.size != cur.size then
              let dv := c.pdiv cur g
              fs := { fs with factors := fs.factors.set! ci (dv, 1) }
              fs := { fs with factors := fs.factors.push (g, 1) }
            if fs.distinct - firstFactor == r then
              done := true
              break
        if done then break
      if done then break
  return (true, fs)

/-- z3 `zp_factor` (:372): full GF(p) factorization — square-free
decomposition, Berlekamp per part (deg > 1), multiplicities multiplied
through. Returns `total_factors > 1` (z3's return value). -/
def zpFactor (c : ZpCtx) (f : Array Int) : Bool × ZpFactors := Id.run do
  let sqFree := zpSquareFreeFactor c f
  let mut fs : ZpFactors := ⟨sqFree.constant, #[]⟩
  for i in [:sqFree.distinct] do
    let (fi, ki) := sqFree.factors[i]!
    if fi.size - 1 > 1 then
      let j0 := fs.distinct
      let (_, fs') := zpFactorSquareFreeBerlekamp c fi fs
      fs := fs'
      -- multiply the new factors' multiplicities by ki
      for j in [j0:fs.distinct] do
        let (pj, kj) := fs.factors[j]!
        fs := { fs with factors := fs.factors.set! j (pj, ki * kj) }
    else
      fs := { fs with factors := fs.factors.push (fi, ki) }
  return (fs.total > 1, fs)

/-! ## Hensel lifting -/

/-- z3 `hensel_lift` (:583), the single quadratic step: given
`U·A + V·B = 1 (mod a)`, `C = A·B (mod b)`, `r = a = b` (as used by
`hensel_lift_quadratic`), produce `A₁ = A (mod b)`, `B₁ = B (mod b)`
with `C = A₁·B₁ (mod b·r)` — Cohen [3] p. 138. -/
def henselLiftStep (a b r : Int) (U A V B C : ZPoly) : ZPoly × ZPoly :=
  let _ := a   -- a = b = r at every call site (kept for source shape)
  -- f := (C − A·B)/b in Z_r[x] (exact division by construction)
  let rc : ZpCtx := ⟨r⟩
  let fz := rc.pnorm (ZPoly.divScalar (ZPoly.sub C (ZPoly.mul A B)) b)
  -- S := (V·f) rem A; T := U·f + B·t  (in Z_r[x])
  let (t, s) := rc.pdivRem (rc.pmul V fz) A
  let tz := rc.padd (rc.pmul U fz) (rc.pmul B t)
  -- A₁ = A + b·S, B₁ = B + b·T (over ℤ)
  (ZPoly.add A (ZPoly.smul s b), ZPoly.add B (ZPoly.smul tz b))

/-- z3 `hensel_lift_quadratic` (:709): lift `C = A·B` from GF(p) to
`Z_{p^e}` (`e` a power of two), maintaining `U·A + V·B = 1`. `A`, `B`
are the GF(p) factors (balanced); the results are balanced mod `p^e`. -/
def henselLiftQuadratic (C : ZPoly) (p : Int) (e : Nat)
    (A B : Array Int) : Array Int × Array Int := Id.run do
  let zp : ZpCtx := ⟨p⟩
  let (u0, v0, _) := zp.pextGcd A B   -- D = 1 (A, B coprime mod p)
  let mut aU := u0; let mut aV := v0
  let mut aA := A; let mut aB := B
  let mut pe := p
  let mut k := 1
  while k < e do
    let zpe : ZpCtx := ⟨pe⟩
    let (aA', aB') := henselLiftStep pe pe pe aU aA aV aB C
    -- g := (1 − A'·U − B'·V)/pe (exact), into Z_{pe}
    let g := zpe.pnorm (ZPoly.divScalar
      (ZPoly.sub (ZPoly.sub #[1] (ZPoly.mul aA' aU)) (ZPoly.mul aB' aV)) pe)
    -- S := g·U + t·B, T := g·V − t·A where (t, T) = divRem(g·V, A)
    let (t, tz) := zpe.pdivRem (zpe.pmul g aV) aA
    let s := zpe.padd (zpe.pmul g aU) (zpe.pmul t aB)
    aU := ZPoly.add aU (ZPoly.smul s pe)
    aV := ZPoly.add aV (ZPoly.smul tz pe)
    -- go quadratic: modulus squares
    pe := pe * pe
    let zpe2 : ZpCtx := ⟨pe⟩
    aU := zpe2.pnorm aU; aV := zpe2.pnorm aV
    aA := zpe2.pnorm aA'; aB := zpe2.pnorm aB'
    k := k * 2
  return (aA, aB)

/-- z3 multi-factor `hensel_lift` (:873): lift the whole GF(p) factor
set of `f` (monic factors, multiplicity 1) to `Z_{p^e}`. The last
factor carries the leading coefficient (`· lc(f)⁻¹`). -/
def henselLift (f : ZPoly) (zpFs : ZpFactors) (p : Int) (e : Nat) : ZpFactors := Id.run do
  let zp : ZpCtx := ⟨p⟩
  let pe : Int := p ^ e
  let zpe : ZpCtx := ⟨pe⟩
  let n := zpFs.distinct
  let mut fParts := f
  let mut out : Array (Array Int × Nat) := #[]
  let mut lastB : Array Int := #[]
  for i in [0:n - 1] do
    let a := zpFs.factors[i]!.1
    -- C: first time the full product × lc(f); afterwards fParts mod p
    let cz :=
      if i == 0 then
        let prod := zpFs.factors.foldl (fun acc (q, _) => zp.pmul acc q) #[1]
        zp.psmul prod (ZPoly.lc f)
      else zp.pnorm fParts
    let b := zp.pdiv cz a
    let (a', b') := henselLiftQuadratic fParts p e a b
    if i == 0 then
      fParts := zpe.pnorm f
    fParts := zpe.pdiv fParts a'
    out := out.push (a', 1)
    lastB := b'
  -- the last factor also contains lc(f)
  let lcInv := zpe.inv (ZPoly.lc f)
  out := out.push (zpe.psmul lastB lcInv, 1)
  return ⟨1, out⟩

/-- z3 `mignotte_bound` (:979): choose the lifting exponent `e` (a power
of two) with `p^e > 2^n·(‖f‖₂ + |lc f|)`, `n = ⌊deg f / 2⌋` — the
binomial coefficients are approximated by `2^(n−1)`, hence `2B` uses
`2^n·(‖f‖ + |lc|)`. -/
def mignotteBound (f : ZPoly) (p : Int) : Nat := Id.run do
  let n := (f.size - 1) / 2
  let sumSq : Int := f.foldl (fun acc c => acc + c * c) 0
  let fNorm : Int := (Nat.sqrt sumSq.natAbs : Int)
  let bound := (2 ^ n : Int) * (fNorm + (ZPoly.lc f).natAbs)
  let mut tmp := p
  let mut e := 1
  while tmp ≤ bound do
    tmp := tmp * tmp
    e := e * 2
  return e

/-! ## Degree sets and the combination iterator -/

/-- z3 `factorization_degree_set`: the set of achievable factorization
degrees, as a bitset (`bit i` ⟺ some sub-product has degree `i`).
`bits` is the bit_vector, `size` its length (max degree + 1). -/
structure DegreeSet where
  bits : Nat
  size : Nat
deriving Repr, Inhabited

namespace DegreeSet

/-- z3's constructor from a factor set (:69): start from `{0}`, and for
each factor copy the set shifted by its degree, once per multiplicity. -/
def ofFactors (factors : Array (Array Int × Nat)) : DegreeSet := Id.run do
  let mut bits := 1
  let mut size := 1
  for (p, k) in factors do
    let deg := p.size - 1
    for _ in [:k] do
      bits := (bits <<< deg) ||| bits
      size := size + deg
  return ⟨bits, size⟩

def maxDegree (ds : DegreeSet) : Nat := ds.size - 1

/-- z3 `is_trivial`: the set is exactly `{0, n}` (no interior bits). -/
def isTrivial (ds : DegreeSet) : Bool :=
  ds.bits &&& ((1 <<< (ds.size - 1)) - 2) == 0

def inSet (ds : DegreeSet) (k : Nat) : Bool :=
  (ds.bits >>> k) &&& 1 == 1

def intersect (ds other : DegreeSet) : DegreeSet :=
  ⟨ds.bits &&& other.bits, min ds.size other.size⟩

end DegreeSet

/-- z3 `ufactorization_combination_iterator` (:127): enumerates
sub-products of the lifted factor set, filtered by the degree set,
with removal of confirmed factors. Indices are `Int` (−1 = none),
`current` padded with `distinct` as in the source. -/
structure CombIter where
  factors : Array (Array Int × Nat)
  degreeSet : DegreeSet
  totalSize : Int
  maxSize : Int
  enabled : Array Bool
  currentSize : Int
  current : Array Int
deriving Inhabited

namespace CombIter

/-- z3's constructor (:164). -/
def init (factors : Array (Array Int × Nat)) (ds : DegreeSet) : CombIter :=
  let n := factors.size
  { factors, degreeSet := ds
    totalSize := n, maxSize := n / 2
    enabled := Array.replicate n true
    currentSize := 0
    current := Array.replicate (n + 1) n }

/-- z3 `find` (:150): the first enabled index in
`(current[position], upperBound)`, or −1. -/
def find (it : CombIter) (position upperBound : Int) : Int := Id.run do
  let mut cur := it.current[position.natAbs]! + 1
  while cur < upperBound && !it.enabled[cur.natAbs]! do
    cur := cur + 1
  if cur == upperBound then return -1
  return cur

/-- Degree of the current selection (:338). -/
def currentDegree (it : CombIter) : Nat := Id.run do
  let mut deg := 0
  for i in [:it.currentSize.natAbs] do
    deg := deg + (it.factors[it.current[i]!.natAbs]!.1.size - 1)
  return deg

/-- z3 `filter_current` (:326): ignore selections whose degree is not
in the degree set. -/
def filterCurrent (it : CombIter) : Bool :=
  !it.degreeSet.inSet it.currentDegree

/-- z3 `next` (:191): advance to the next combination; when
`removeCurrent`, the current selection is disabled first (a confirmed
factor was extracted). Returns false when exhausted. -/
def next (it : CombIter) (removeCurrent : Bool) : CombIter × Bool := Id.run do
  let mut it := it
  let mut remove := removeCurrent
  let maxUB : Int := it.factors.size
  let mut filtered := true
  let mut ok := true
  while filtered && ok do
    let mut currentI := it.currentSize - 1
    let mut currentValue : Int := -1
    if remove then
      -- disable the elements of the current selection
      let mut ci := it.currentSize - 1
      while ci > 0 do
        it := { it with
          enabled := it.enabled.set! it.current[ci.natAbs]!.natAbs false
          current := it.current.set! ci.natAbs maxUB }
        ci := ci - 1
      it := { it with enabled := it.enabled.set! it.current[0]!.natAbs false }
      remove := false
      it := { it with
        totalSize := it.totalSize - it.currentSize
        maxSize := (it.totalSize - it.currentSize) / 2 }
    -- go back to the first position that can be increased
    while currentI ≥ 0 do
      currentValue := it.find currentI.natAbs (it.current[(currentI.natAbs + 1)]!)
      if currentValue ≥ 0 then
        it := { it with current := it.current.set! currentI.natAbs currentValue }
        break
      else
        currentI := currentI - 1
    -- inner do-while: complete the selection (or grow it)
    let mut inner := true
    while inner do
      if currentValue == -1 then
        if it.currentSize ≥ it.maxSize then
          ok := false; break
        it := { it with currentSize := it.currentSize + 1 }
        it := { it with current := it.current.set! 0 (-1) }
        currentI := 0
        currentValue := it.find 0 maxUB
        if currentValue == -1 then
          ok := false; break
        it := { it with current := it.current.set! 0 currentValue }
      -- complete the remaining positions
      currentI := currentI + 1
      while currentI < it.currentSize do
        it := { it with current :=
          it.current.set! currentI.natAbs (it.current[(currentI.natAbs - 1)]!) }
        currentValue := it.find currentI.natAbs maxUB
        if currentValue == -1 then
          it := { it with current := it.current.set! 0 (-1) }
          break
        it := { it with current := it.current.set! currentI.natAbs currentValue }
        currentI := currentI + 1
      if currentValue != -1 then
        inner := false
    if ok then
      filtered := it.filterCurrent
  return (it, ok)

/-- z3 `left` (:347): the product of the selected factors (in the
lifted modulus). -/
def left (it : CombIter) (zpe : ZpCtx) : Array Int := Id.run do
  let mut out := it.factors[it.current[0]!.natAbs]!.1
  for i in [1:it.currentSize.natAbs] do
    out := zpe.pmul out it.factors[it.current[i]!.natAbs]!.1
  return out

/-- z3 `right` (:389): the product of the enabled, non-selected
factors (in index order). -/
def right (it : CombIter) (zpe : ZpCtx) : Array Int := Id.run do
  let n := it.factors.size
  let mut out : Array Int := #[]
  let mut selI := 0
  for cur in [:n] do
    if it.enabled[cur]! then
      if selI ≥ it.currentSize.natAbs || (cur : Int) < it.current[selI]! then
        out := if out.isEmpty then it.factors[cur]!.1 else zpe.pmul out it.factors[cur]!.1
      else
        selI := selI + 1
  return out

/-- z3 `get_left_tail_coeff` (:356): `m · ∏ (selected constant terms)`. -/
def getLeftTailCoeff (it : CombIter) (zpe : ZpCtx) (m : Int) : Int := Id.run do
  let mut out := m
  for i in [:it.currentSize.natAbs] do
    out := zpe.mul out (it.factors[it.current[i]!.natAbs]!.1.getD 0 0)
  return out

/-- z3 `get_right_tail_coeff` (:364): `m · ∏ (unselected constant terms)`. -/
def getRightTailCoeff (it : CombIter) (zpe : ZpCtx) (m : Int) : Int := Id.run do
  let n := it.factors.size
  let mut out := m
  let mut selI := 0
  for cur in [:n] do
    if it.enabled[cur]! then
      if selI ≥ it.currentSize.natAbs || (cur : Int) < it.current[selI]! then
        out := zpe.mul out (it.factors[cur]!.1.getD 0 0)
      else
        selI := selI + 1
  return out

end CombIter

/-- Total degree of a GF(p) factorization (z3 `zp_factors::get_degree`). -/
def ZpFactors.degreeSum (fs : ZpFactors) : Nat :=
  fs.factors.foldl (fun acc (p, k) => acc + (p.size - 1) * k) 0

/-! ## The ℤ[x] driver -/

/-- Factor set over ℤ (z3 `factors`): `f = constant · ∏ polyᵢ^kᵢ`. -/
structure ZFactors where
  constant : Int
  factors : Array (ZPoly × Nat)
deriving Repr, Inhabited, BEq

namespace ZFactors

def empty : ZFactors := ⟨1, #[]⟩

def push (fs : ZFactors) (p : ZPoly) (k : Nat) : ZFactors :=
  { fs with factors := fs.factors.push (p, k) }

end ZFactors

/-- z3 `factor_params` with the DEFAULTS (`algebraic_params.pyg`:
`factor_num_primes = 1`, `factor_max_prime = 31`,
`factor_search_size = 5000`). -/
structure FactorParams where
  pTrials : Nat := 1
  maxP : Nat := 31
  maxSearchSize : Nat := 5000
deriving Repr, Inhabited

/-- The small-prime iterator's sequence up to the default `max_p`
(z3 `prime_iterator`: 2, 3, 5, …). -/
def smallPrimes : List Int := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- z3 `factor_square_free` (:1019): factor a primitive square-free
ℤ[x] polynomial via GF(p) factorization + Hensel lifting + trial
recombination. `k` is the Yun multiplicity the factors should carry;
`fs` accumulates. Returns `false` when the search budget was exceeded
(the pushed factors are then not guaranteed complete — z3's caller
uses the return value as the `m_minimal` flag, so we must match it
exactly). -/
def factorSquareFree (f : ZPoly) (k : Nat) (fs : ZFactors)
    (params : FactorParams := {}) : Bool × ZFactors := Id.run do
  let mut fs := fs
  -- positive leading coefficient (flip the constant if k is odd)
  let mut fpp := f
  if ZPoly.lc fpp < 0 then
    fpp := ZPoly.neg fpp
    if k % 2 == 1 then
      fs := { fs with constant := -fs.constant }
  -- prime trials
  let mut zpFs : ZpFactors := ⟨1, #[]⟩
  let mut zpFsP : Int := 2
  let mut degreeSet : Option DegreeSet := none
  let mut trials := 0
  let mut bail : Option (Bool × ZFactors) := none
  for p in smallPrimes do
    if bail.isNone && trials ≤ params.pTrials then
      if Int.gcd p (ZPoly.lc fpp) != 1 then
        pure ()   -- bad prime: lc vanishes
      else
        let zp : ZpCtx := ⟨p⟩
        let fppZp0 := zp.pnorm fpp
        if !zp.pisSquareFree fppZp0 then
          pure ()   -- bad prime: not square-free mod p
        else
          let fppZp := zp.pmkMonic fppZp0
          let (factored, currentFs) := zpFactorSquareFreeBerlekamp zp fppZp ⟨1, #[]⟩
          if !factored then
            -- irreducible over GF(p) ⇒ irreducible over ℤ
            bail := some (true, fs.push fpp k)
          else
            let cds := DegreeSet.ofFactors currentFs.factors
            let ds := match degreeSet with
              | none => cds
              | some ds => ds.intersect cds
            degreeSet := some ds
            if ds.isTrivial then
              bail := some (true, fs.push fpp k)
            else
              trials := trials + 1
              if zpFs.distinct == 0 || zpFs.total > currentFs.total then
                zpFs := currentFs
                zpFsP := p
  match bail with
  | some r => return r
  | none =>
  -- note: exhausting smallPrimes below pTrials without a candidate is
  -- the z3 `next_prime > m_max_p` path: give up, push unfactored
  if zpFs.distinct == 0 then
    return (false, fs.push fpp k)
  -- lift and recombine
  let e := mignotteBound fpp zpFsP
  let zpeFs := henselLift fpp zpFs zpFsP e
  let pe : Int := zpFsP ^ e
  let zpe : ZpCtx := ⟨pe⟩
  let mut fppLc := ZPoly.lc fpp
  let mut fppM := ZPoly.smul fpp fppLc   -- f_pp := f_pp · lc(f_pp)
  let ds := degreeSet.get!
  let mut it := CombIter.init zpeFs.factors ds
  let mut counter := 0
  let mut result := true
  let mut remove := false
  let mut searching := true
  while searching do
    let (it', hasNext) := it.next remove
    it := it'
    if !hasNext then
      searching := false
    else
      counter := counter + 1
      if counter > params.maxSearchSize then
        result := false
        searching := false
      else
        let usingLeft := it.currentDegree ≤ zpFs.degreeSum / 2
        let (tmp, trial0) :=
          if usingLeft then
            (it.getLeftTailCoeff zpe fppLc, it.left zpe)
          else
            (it.getRightTailCoeff zpe fppLc, it.right zpe)
        if !ZPoly.dvdInt tmp (ZPoly.coeff fppM 0) then
          remove := false
        else
          let trial := zpe.psmul trial0 fppLc
          match ZPoly.exactDiv fppM trial with
          | none =>
            remove := false
          | some quo =>
            let trueFactor := if usingLeft then trial else quo
            let (trialPrim, _) := ZPoly.getPrimitiveAndContent trueFactor
            fs := fs.push trialPrim k
            let (quoPrim, _) := ZPoly.getPrimitiveAndContent quo
            fppLc := ZPoly.lc quoPrim
            fppM := ZPoly.smul quoPrim fppLc
            remove := true
  -- what's left (if not a constant)
  if fppM.size > 1 then
    fs := fs.push (ZPoly.divScalar fppM fppLc) k
  return (result, fs)

/-- z3 `factor_2_sqf_pp` (:2980): the degree-2 shortcut — discriminant
perfect square splits into the two linear factors (content-normalized);
otherwise irreducible. Precondition: deg 2, square-free (disc ≠ 0). -/
def factor2SqfPp (p : ZPoly) (fs : ZFactors) (k : Nat) : ZFactors :=
  let a := ZPoly.coeff p 2
  let b := ZPoly.coeff p 1
  let cc := ZPoly.coeff p 0
  let disc := b * b - 4 * a * cc
  if disc ≤ 0 then
    fs.push p k   -- irreducible (disc ≠ 0 by square-freeness)
  else
    let s := (Nat.sqrt disc.natAbs : Int)
    if s * s != disc then
      fs.push p k
    else
      let f1 := ZPoly.normalize #[b - s, 2 * a]
      let f2 := ZPoly.normalize #[b + s, 2 * a]
      (fs.push f1 k).push f2 k

/-- z3 `factor_sqf_pp` (:3026): linear ⇒ push; quadratic ⇒ the
discriminant shortcut; otherwise the full pipeline. -/
def factorSqfPp (p : ZPoly) (fs : ZFactors) (k : Nat)
    (params : FactorParams := {}) : Bool × ZFactors :=
  if p.size ≤ 2 then
    (true, fs.push p k)
  else if p.size == 3 then
    (true, factor2SqfPp p fs k)
  else
    factorSquareFree p k fs params

/-- z3 `flip_factor_sign_if_lm_neg` (:3045). -/
def flipFactorSignIfLmNeg (p : ZPoly) (fs : ZFactors) (k : Nat) : ZPoly × ZFactors :=
  if ZPoly.lc p < 0 then
    (ZPoly.neg p, if k % 2 == 1 then { fs with constant := -fs.constant } else fs)
  else (p, fs)

/-- z3 `is_const`: size ≤ 1. -/
def ZPoly.isConst (p : ZPoly) : Bool := p.size ≤ 1

/-- z3 `factor_core` (:3053): content extraction, then the Yun-style
square-free decomposition over ℤ (gcd with derivative chain), each
square-free component factored by `factor_sqf_pp` with its
multiplicity. Returns `false` iff some component's search was
incomplete (⇒ cells built from it must not be marked minimal). -/
def factorCore (f : ZPoly) (fs : ZFactors)
    (params : FactorParams := {}) : Bool × ZFactors := Id.run do
  if f.isEmpty then
    return (true, { fs with constant := 0 })
  if f.size == 1 then
    return (true, { fs with constant := f[0]! })
  let (pp, content) := ZPoly.getPrimitiveAndContent f
  let mut fs := { fs with constant := content * fs.constant }
  let mut result := true
  let cPrime := ZPoly.derivative pp
  let b0 := ZPoly.gcd pp cPrime
  if b0.isConst then
    -- pp is square-free
    let (c, fs') := flipFactorSignIfLmNeg pp fs 1
    fs := fs'
    let (ok, fs'') := factorSqfPp c fs 1 params
    fs := fs''
    result := ok
  else
    let mut a := (ZPoly.exactDiv pp b0).get!
    let mut b := b0
    let mut j := 1
    while !a.isConst do
      let d := ZPoly.gcd a b
      let c := (ZPoly.exactDiv a d).get!
      if !c.isConst then
        let (c', fs') := flipFactorSignIfLmNeg c fs j
        fs := fs'
        let (ok, fs'') := factorSqfPp c' fs j params
        fs := fs''
        if !ok then result := false
      else
        if c == #[-1] && j % 2 == 1 then
          fs := { fs with constant := -fs.constant }
      b := (ZPoly.exactDiv b d).get!
      a := d
      j := j + 1
  return (result, fs)

/-- z3 `manager::factor` (:3126): full ℤ[x] factorization —
`f = constant · ∏ polyᵢ^kᵢ`, each `polyᵢ` irreducible with positive
leading coefficient (when the search completed). The Bool is z3's
return value: `false` means INCOMPLETE (search budget), which the
algebraic-numbers layer consumes as "not minimal". -/
def factor (f : ZPoly) (params : FactorParams := {}) : Bool × ZFactors :=
  factorCore f ZFactors.empty params

end LeanNonlinearArith.Kernel
