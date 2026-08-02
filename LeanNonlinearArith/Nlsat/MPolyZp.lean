import LeanNonlinearArith.Nlsat.MPolyOps

/-!
# nla-12d.1b-iii — the Zp-mode layer (z3 `polynomial.cpp`/`polynomial_cache.cpp` @ **4.12.5**)

The pieces of the multivariate modular gcd that operate in Zp mode on
the shared `MPoly` representation (z3's `mpzzp_manager` mode flag =
our `NumMode`, generalized in `MPolyOps.lean`):

* `managerNormalize` — z3 `normalize` (:5781): balanced p-normalize in
  Zp mode, INTEGER-CONTENT strip in ℤ mode (both used by mod_gcd).
* `univEval`/`substitute1`/`mkGlexMonic` — evaluation, numeral
  substitution (:6237), monic normalization in the prime field.
* `lcGlexZpX` (:4060) — leading coefficient (glex) viewed in
  Zp[y…][x].
* `NewtonInterpolator` (:2850) — the dense interpolation engine.
* `Skeleton`/`SparseInterpolator` (:3010/:3115) + `LinearEqSolver`
  (`linear_eq_solver.h`) — the sparse interpolation engine (skeleton
  is a support cache; results are verified downstream).
* `craCombineImagesM` (:3700s) — multivariate CRA (ℤ-mode numeral
  work, balanced output), mirroring nla-27's univariate
  `ZPoly.craCombineImages`.
* `peekFresh` (:4096) — z3 draws `rand() % p` (libc rand with no
  srand anywhere in z3's src — the sequence is platform-libc-
  dependent, i.e. z3 itself is not cross-platform faithful here).
  Ported as the first fresh natural: **output-independence argument —
  every candidate produced via sampled values is verified by
  `divides` before returning (mod_gcd_rec :4245-4252), so the sample
  sequence affects only which candidates are tried, never the
  returned gcd** (registered for Danielle's sign-off; also satisfies
  the determinism directive).
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

namespace MPoly

/-- z3 `manager::normalize` (:5781): Zp mode ⇒ balanced p-normalize;
ℤ mode ⇒ divide out the integer content gcd. -/
def managerNormalize (mode : NumMode) (p : MPoly) : MPoly :=
  match mode with
  | some c => pNorm (some c) p
  | none =>
    match p with
    | [] => []
    | _ =>
      let g := p.ic
      if g == 1 then p
      else p.map fun (a, m) => (a / g, m)

/-- z3 `univ_eval` (:6409): Horner evaluation of a univariate `p` at
`val` in mode arithmetic. -/
def univEval (mode : NumMode) (p : MPoly) (x : Var) (val : Int) : Int :=
  let cs := p.coeffsIn x
  let d := cs.size - 1
  (List.range d).reverse.foldl (fun r i =>
    mode.add (mode.mul r val) (cs[i]!.asConst?.getD 0))
    (mode.norm (cs[d]!.asConst?.getD 0))

/-- z3 `substitute(p, 1, &x, &val)` (:6237, single-variable numeral
substitution): each term's coefficient picks up `val^k`, `x` is
stripped. -/
def substitute1 (mode : NumMode) (p : MPoly) (x : Var) (val : Int) : MPoly :=
  p.foldl (fun acc (a, m) =>
    let k := m.degreeIn x
    addM mode acc [(mode.mul a (mode.pow val k), m.erase x)]) []

/-- z3 `mk_glex_monic` (:6565): multiply through by the inverse of the
glex-maximal coefficient (prime field). -/
def mkGlexMonic (c : ZpCtx) (p : MPoly) : MPoly :=
  match p.glexMaxTerm with
  | none => p
  | some (a, _) =>
    if a == 1 then p
    else pNorm (some c) (p.map fun (b, m) => (c.mul b (c.inv a), m))

/-- z3 `lc_glex_ZpX` (:4060): the leading coefficient of `p` viewed as
a polynomial over `x` — the `a·x^k` terms whose x-stripped monomial is
glex-maximal. -/
def lcGlexZpX (p : MPoly) (x : Var) : MPoly :=
  let stripped : MPoly → List (Int × Monomial × Monomial) := fun p =>
    p.map fun (a, m) => (a, m, m.erase x)
  match (stripped p).foldl (fun acc (_, _, sm) =>
      match acc with
      | none => some sm
      | some m' => if Monomial.gradedLexCompare sm m' == .gt then some sm else acc)
      none with
  | none => []
  | some maxSm =>
    (stripped p).foldl (fun acc (a, m, sm) =>
      if sm == maxSm then add acc [(a, [(x, m.degreeIn x)].filter (·.2 != 0))]
      else acc) []

end MPoly

/-! ## peek_fresh -/

/-- z3 `peek_fresh` (:4096), ported as the first fresh natural (see the
header for the output-independence argument; z3's own `rand() % p` is
platform-libc-dependent and unseeded). -/
def peekFresh (vals : Array Int) : Int := Id.run do
  let mut v : Int := 0
  while vals.contains v do
    v := v + 1
  return v

/-! ## Newton interpolation (:2850) -/

/-- z3 `newton_interpolator`: incremental Newton-form interpolation of
a polynomial in `x` over Zp, from (input, output) samples. -/
structure NewtonInterpolator (c : ZpCtx) where
  inputs : Array Int := #[]
  invs : Array Int := #[0]   -- z3 seeds m_invs with a single 0
  vs : Array MPoly := #[]
deriving Inhabited

namespace NewtonInterpolator

/-- z3 `reset`. -/
def reset {c : ZpCtx} : NewtonInterpolator c := {}

/-- z3 `num_sample_points`. -/
def numSamplePoints {c : ZpCtx} (ni : NewtonInterpolator c) : Nat := ni.inputs.size

/-- z3 `add(input, output)` (:2873): extend the divided-difference
table. Pre: `input` differs from all previous inputs (z3 SASSERTs —
`peek_fresh` + the lc_g-val skip maintain it). -/
def add {c : ZpCtx} (ni : NewtonInterpolator c) (input : Int) (output : MPoly) :
    NewtonInterpolator c := Id.run do
  let sz := ni.numSamplePoints
  if sz == 0 then
    return { ni with inputs := ni.inputs.push input, vs := ni.vs.push output }
  -- product := Π (input − inputs[i])
  let mut product : Int := c.norm 1
  for i in [:sz] do
    product := c.mul product (c.sub input ni.inputs[i]!)
  let pinv := c.inv product
  -- Newton coefficient: temp = vs[sz-1]; temp <- (input−inputs[j])·temp + vs[j]
  let mut temp : MPoly := ni.vs[sz - 1]!
  for j in (List.range (sz - 1)).reverse do
    let aux : MPoly := MPoly.ofInt (c.sub input ni.inputs[j]!)
    temp := MPoly.addM (some c) (MPoly.mulM (some c) aux temp) ni.vs[j]!
  let newV := MPoly.mulM (some c) (MPoly.ofInt pinv)
    (MPoly.subM (some c) output temp)
  return { inputs := ni.inputs.push input
         , invs := ni.invs.push pinv
         , vs := ni.vs.push newV }

/-- z3 `mk(x, r)` (:2927): Newton form → standard form. -/
def mkPoly {c : ZpCtx} (ni : NewtonInterpolator c) (x : Var) : MPoly := Id.run do
  let d := ni.numSamplePoints - 1
  let mut u : MPoly := ni.vs[d]!
  for k in (List.range d).reverse do
    let lin : MPoly := MPoly.addM (some c) (MPoly.ofVar x)
      (MPoly.ofInt (c.norm (-ni.inputs[k]!)))
    u := MPoly.addM (some c) (MPoly.mulM (some c) u lin) ni.vs[k]!
  return u

end NewtonInterpolator

/-! ## Skeleton + sparse interpolation (:3010/:3115) -/

/-- z3 `skeleton`: the monomial support of a `Zp[Y…][x]` polynomial —
x-stripped monomials with the list of x-powers (and original
monomials) attached to each. A pure support CACHE (results are
verified downstream by `divides`). -/
structure Skeleton where
  x : Var
  entries : Array (Monomial × Nat × Nat) := #[]  -- (stripped, firstIdx, numPowers)
  powers : Array Nat := #[]
  origMonomials : Array Monomial := #[]
  maxPowers : Nat := 0
deriving Inhabited

namespace Skeleton

/-- z3 `skeleton(p, x)` (:3024): group terms by x-stripped monomial
(sorted ascending `lex_compare`, powers ascending within a group —
z3's `lex_lt2(x)` sort; grouping order is cosmetic here since result
polynomials are re-canonicalized). -/
def build (p : MPoly) (x : Var) : Skeleton := Id.run do
  let sorted := p.mergeSort (fun (_, m1) (_, m2) =>
    let sm1 := m1.erase x
    let sm2 := m2.erase x
    Monomial.lexCompare sm1 sm2 == .lt ||
    (sm1 == sm2 && m1.degreeIn x < m2.degreeIn x))
  let mut entries : Array (Monomial × Nat × Nat) := #[]
  let mut powers : Array Nat := #[]
  let mut origs : Array Monomial := #[]
  let mut maxPowers : Nat := 0
  for (_, m) in sorted do
    let sm := m.erase x
    let k := m.degreeIn x
    match entries.back? with
    | some (pm, fi, np) =>
      if pm == sm then
        let np' := np + 1
        entries := entries.set! (entries.size - 1) (pm, fi, np')
        if np' > maxPowers then maxPowers := np'
      else
        entries := entries.push (sm, powers.size, 1)
        if maxPowers == 0 then maxPowers := 1
    | none =>
      entries := entries.push (sm, powers.size, 1)
      if maxPowers == 0 then maxPowers := 1
    powers := powers.push k
    origs := origs.push m
  return { x, entries, powers, origMonomials := origs, maxPowers }

/-- z3 `get_entry_idx` (structural monomial equality — z3 compares
pointers post-hash-consing). -/
def getEntryIdx (sk : Skeleton) (m : Monomial) : Option Nat :=
  sk.entries.findIdx? (·.1 == m)

end Skeleton

/-- z3 `linear_eq_solver<mpzzp_manager>` (`linear_eq_solver.h`):
dense Gaussian elimination over the prime field. `A` starts zeroed
n×n; rows are set by `add`. -/
structure LinearEqSolver (c : ZpCtx) where
  n : Nat
  A : Array (Array Int) := Array.replicate n (Array.replicate n 0)
  b : Array Int := Array.replicate n 0
deriving Inhabited

namespace LinearEqSolver

/-- z3 `add(i, as, b)`: set row i. -/
def setRow {c : ZpCtx} (s : LinearEqSolver c) (i : Nat) (as : Array Int) (bi : Int) :
    LinearEqSolver c :=
  { s with A := s.A.set! i as, b := s.b.set! i bi }

/-- z3 `solve(xs)` (:86): pivot-normalize-eliminate then back-
substitute. `none` on singular. -/
def solve {c : ZpCtx} (s : LinearEqSolver c) : Option (Array Int) := Id.run do
  let n := s.n
  let mut A := s.A
  let mut b := s.b
  for k in [:n] do
    -- find pivot
    let mut i := k
    while i < n && A[i]![k]! == 0 do
      i := i + 1
    if i == n then
      return none
    let (ak, ai) := (A[k]!, A[i]!)
    A := (A.set! k ai).set! i ak
    let (bk, bi) := (b[k]!, b[i]!)
    b := (b.set! k bi).set! i bk
    -- normalize row k
    let akk := A[k]![k]!
    for j in [k+1:n] do
      A := A.set! k (A[k]!.set! j (NumMode.div (some c) A[k]![j]! akk))
    b := b.set! k (NumMode.div (some c) b[k]! akk)
    A := A.set! k (A[k]!.set! k 1)
    -- eliminate below (z3 `submul(A_i[j], A_i_k, A_k[j], A_i[j])` =
    -- `A_i[j] − A_i_k·A_k[j]` — mind `ZpCtx.submul`'s (a, b, out) order)
    for i2 in [k+1:n] do
      let aik := A[i2]![k]!
      for j in [k+1:n] do
        A := A.set! i2 (A[i2]!.set! j (c.submul aik A[k]![j]! A[i2]![j]!))
      b := b.set! i2 (c.submul aik b[k]! b[i2]!)
      A := A.set! i2 (A[i2]!.set! k 0)
  -- back substitute
  let mut xs := Array.replicate n 0
  for k in (List.range n).reverse do
    xs := xs.set! k b[k]!
    for i in (List.range k).reverse do
      b := b.set! i (c.submul A[i]![k]! b[k]! b[i]!)
  return xs

end LinearEqSolver

/-- z3 `sparse_interpolator` (:3115): solve for the coefficients of a
known-support polynomial (its skeleton) from `max_num_powers` samples.
`outputs` is flat over `sk.powers` (z3's layout). -/
structure SparseInterpolator (c : ZpCtx) where
  sk : Skeleton
  inputs : Array Int := #[]
  outputs : Array Int := #[]
deriving Inhabited

namespace SparseInterpolator

/-- Smart constructor (z3's ctor pre-sizes `m_outputs` over the flat
powers layout). -/
def ofSkeleton {c : ZpCtx} (sk : Skeleton) : SparseInterpolator c :=
  { sk, outputs := Array.replicate sk.powers.size 0 }

/-- z3 `reset`. -/
def reset {c : ZpCtx} (si : SparseInterpolator c) : SparseInterpolator c :=
  { si with inputs := #[] }

/-- z3 `ready`. -/
def ready {c : ZpCtx} (si : SparseInterpolator c) : Bool :=
  si.inputs.size == si.sk.maxPowers

/-- z3 `add(in, q)` (:3142): record q's coefficients against the
skeleton entries. `false` (z3) = q's support escapes the skeleton ⇒
`sparse_mgcd_failed`. -/
def add {c : ZpCtx} (si : SparseInterpolator c)
    (inp : Int) (q : MPoly) : Option (SparseInterpolator c) := Id.run do
  let inputIdx := si.inputs.size
  let mut outputs := si.outputs
  for (a, mon) in q do
    match si.sk.getEntryIdx mon with
    | none => return none
    | some eidx =>
      let (_, fi, np) := si.sk.entries[eidx]!
      if inputIdx < np then
        outputs := outputs.set! (fi + inputIdx) a
  return some { si with inputs := si.inputs.push inp, outputs }

/-- z3 `mk(r)` (:3168): per skeleton entry, solve the Vandermonde
system for the coefficient powers; `false` (singular) ⇒
`sparse_mgcd_failed`. -/
def mkPoly {c : ZpCtx} (si : SparseInterpolator c) : Option MPoly := Id.run do
  let sk := si.sk
  let mut r : MPoly := []
  for eidx in [:sk.entries.size] do
    let (_, fi, np) := sk.entries[eidx]!
    let mut solver : LinearEqSolver c := { n := np }
    for i in [:np] do
      let inp := si.inputs[i]!
      let cs : Array Int := Array.ofFn (n := np) fun j =>
        NumMode.pow (some c) inp sk.powers[fi + j.val]!
      solver := solver.setRow i cs si.outputs[fi + i]!
    match solver.solve with
    | none => return none
    | some newAs =>
      for i in [:np] do
        if newAs[i]! != 0 then
          r := MPoly.addM (some c) r [(newAs[i]!, sk.origMonomials[fi + i]!)]
  return some r

end SparseInterpolator

/-! ## Multivariate CRA (:3700s) -/

/-- z3 `CRA_combine_images` (:3700s): combine term images `C1 mod b1`
and `C2 mod b2` into `R mod b1·b2` with balanced representatives —
the multivariate analogue of nla-27's `ZPoly.craCombineImages`
(same Bézout/multiplicator/balancing arithmetic, over the merged
term lists). Returns `(R, b1·b2)`. Pre: `gcd(b1, b2) = 1`, both odd
(z3 SASSERTs). -/
def craCombineImagesM (C1 : MPoly) (b1 : Int) (C2 : MPoly) (b2 : Int) : MPoly × Int := Id.run do
  let (inv1', inv2') := ZpCtx.bezoutCoeffs b1 b2
  let inv1 := inv1' % b2
  let inv2 := inv2' % b1
  let a1 := b2 * inv2   -- multiplier for C1 coefficients
  let a2 := b1 * inv1   -- multiplier for C2 coefficients
  let newBound := b1 * b2
  let upper := newBound / 2
  let addTerm (r : MPoly) (A1 A2 : Int) (m : Monomial) : MPoly :=
    let newA0 := (A1 * a1 + A2 * a2) % newBound
    let newA := if newA0 > upper then newA0 - newBound else newA0
    MPoly.add r [(newA, m)]
  -- 3-way merge over the canonical (descending lexCompare) term lists
  let mut r : MPoly := []
  let mut l1 := C1
  let mut l2 := C2
  while true do
    match l1, l2 with
    | [], [] => break
    | [], (a2', m2) :: t2 =>
      r := addTerm r 0 a2' m2
      l2 := t2
    | (a1', m1) :: t1, [] =>
      r := addTerm r a1' 0 m1
      l1 := t1
    | (a1', m1) :: t1, (a2', m2) :: t2 =>
      match Monomial.lexCompare m1 m2 with
      | .eq =>
        r := addTerm r a1' a2' m1
        l1 := t1
        l2 := t2
      | .gt =>
        r := addTerm r a1' 0 m1
        l1 := t1
      | .lt =>
        r := addTerm r 0 a2' m2
        l2 := t2
  return (r, newBound)

end LeanNonlinearArith.Nlsat
