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

end LeanNonlinearArith.Kernel
