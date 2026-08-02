import LeanNonlinearArith.Nlsat.MPolyGcd
import LeanNonlinearArith.Kernel.Factor

/-!
# nla-12d.1b-v — multivariate factorization (z3 `polynomial.cpp` `factor_core` @ **4.12.5**)

`manager::factor` (:6700) → `factor_core` (:6628): min-degree-var
content extraction (`iccpM`), then Yun square-free decomposition over
the primitive part, dispatching each square-free piece
(`factor_sqf_pp` :6610):

* deg 1 ⇒ push as-is (`factor_1_sqf_pp` :6465);
* **univariate** ⇒ `factor_sqf_pp_univ` (:6558) — bridge to nla-27's
  `Factor.factorSquareFree` (the `upolynomial::factor_square_free`
  port), factors converted back, multiplicities composed, `fs`
  constant ±1 sign folded when `k` is odd;
* deg 2 (multivariate) ⇒ `factor_2_sqf_pp` (:6474) — discriminant
  perfect-square attempt via `MPoly.sqrt`, with z3's `flipped_coeffs`
  sign bookkeeping; non-square disc ⇒ irreducible;
* deg > 2 (multivariate) ⇒ pushed back UNFACTORED (`factor_n_sqf_pp`
  :6600 — z3's own "TODO: invoke Dejan's procedure").

The `factors` record (:1626) accumulates a constant (integer content,
content signs, disc-flip signs — DROPPED by the cache view) and
`(poly, multiplicity)` pairs. `factorDistinct` is the
`polynomial::cache::factor` view: distinct polys only.
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-- z3 `manager::factors` (:1626): a constant plus `(poly,
multiplicity)` pairs. -/
structure MFactors where
  constant : Int := 1
  factors : Array (MPoly × Nat) := #[]
deriving Inhabited, BEq

namespace MFactors

/-- z3 `acc_constant` (:6451). -/
def accConstant (fs : MFactors) (c : Int) : MFactors :=
  { fs with constant := fs.constant * c }

/-- z3 `flip_sign` (:6458) — flips the CONSTANT only. -/
def flipSign (fs : MFactors) : MFactors :=
  { fs with constant := -fs.constant }

/-- z3 `factors::push_back` (:1645). -/
def push (fs : MFactors) (p : MPoly) (k : Nat) : MFactors :=
  { fs with factors := fs.factors.push (p, k) }

end MFactors

namespace MPoly

/-- MPoly univariate in `x` → dense ascending ZPoly (z3
`up_manager::to_numeral_vector`). `none` if other variables remain. -/
def toZPoly? (p : MPoly) (x : Var) : Option ZPoly := Id.run do
  let mut out : Array Int := #[]
  for c in p.coeffsIn x do
    match c.asConst? with
    | some a => out := out.push a
    | none => return none
  return some out

/-- z3 `to_polynomial` (:6698): dense ascending coeffs → MPoly in `x`. -/
def ofZPoly (f : ZPoly) (x : Var) : MPoly := Id.run do
  let mut out : MPoly := []
  for i in [:f.size] do
    if f[i]! != 0 then
      out := add out [(f[i]!, if i == 0 then [] else [(x, i)])]
  return out

/-- z3 `pp(p, x)` (:3583): primitive part w.r.t. `x` (iccp wrapper, ℤ
mode). -/
def ppM (p : MPoly) (x : Var) : MPoly := (iccpM none p x).2.2

/-- z3 `factor_2_sqf_pp` (:6474): discriminant perfect-square attempt
on a square-free primitive quadratic in `x`. -/
def factor2SqfPp (p : MPoly) (fs : MFactors) (x : Var) (k : Nat) : MFactors :=
  let cs := p.coeffsIn x
  let (a0, b0, c0) := (cs[2]!, cs[1]!, cs[0]!)
  -- make the leading monomial of a positive (z3's graded_lex_max_pos)
  let (a, b, cc, flipped) :=
    match a0.glexMaxTerm with
    | some (am, _) =>
      if am < 0 then (a0.neg, b0.neg, c0.neg, true) else (a0, b0, c0, false)
    | none => (a0, b0, c0, false)   -- SASSERT !is_zero(a)
  let disc := (b.mul b).sub ((ofInt 4).mul (a.mul cc))
  match disc.sqrt with
  | none => fs.push p k   -- irreducible
  | some dsq =>
    let fs := if flipped && k % 2 == 1 then fs.flipSign else fs
    let twoAx := smulTerm 2 [(x, 1)] a
    let f1 := ((twoAx.add b).sub dsq).ppM x
    let f2 := ((twoAx.add b).add dsq).ppM x
    (fs.push f1 k).push f2 k

/-- z3 `factor_sqf_pp_univ` (:6558): univariate square-free piece via
nla-27 (`upolynomial::factor_square_free`). -/
def factorSqfPpUniv (p : MPoly) (fs : MFactors) (x : Var) (k : Nat) : MFactors :=
  let fZ := (p.toZPoly? x).get!   -- SASSERT is_univariate(p)
  let (_, zfs) := factorSquareFree fZ 1 ZFactors.empty
  if zfs.factors.size == 1 && zfs.factors[0]!.2 == 1 then
    fs.push p k   -- irreducible (also the give-up shape)
  else
    let fs := zfs.factors.foldl (fun acc (f1, k1) =>
      acc.push (ofZPoly f1 x) (k * k1)) fs
    if zfs.constant == -1 && k % 2 == 1 then fs.flipSign else fs

/-- z3 `factor_sqf_pp` (:6610) dispatch. -/
def factorSqfPp (p : MPoly) (fs : MFactors) (x : Var) (k : Nat) : MFactors :=
  let degX := p.degreeIn x
  if degX == 1 then fs.push p k                        -- factor_1_sqf_pp
  else if p.varDegrees.size == 1 then factorSqfPpUniv p fs x k
  else if degX == 2 then factor2SqfPp p fs x k
  else fs.push p k   -- factor_n_sqf_pp: z3's TODO — pushed back unfactored

/-- z3 `factor_core` (:6628): content extraction + Yun square-free
decomposition. -/
partial def factorCore (p : MPoly) (fs : MFactors) : MFactors :=
  match p.asConst? with
  | some a => fs.accConstant a
  | none =>
    let x := p.getMinDegreeVar.get!
    let (i, c, pp) := iccpM none p x
    let fs := fs.accConstant i
    let fs := factorCore c fs
    yun pp fs x
where
  yun (C : MPoly) (fs : MFactors) (x : Var) : MFactors :=
    let C' := C.derivative x
    let B := gcdM none C C'
    if B.asConst?.isSome then factorSqfPp C fs x 1
    else loop (C.exactDiv B) B fs x 1
  /-- The Yun loop (:6656-6696): `A` = P_j·…·P_k, `B` = P_{j+1}·…. -/
  loop (A B : MPoly) (fs : MFactors) (x : Var) (j : Nat) : MFactors :=
    if A.asConst?.isSome then fs
    else
      let D := gcdM none A B
      let C := A.exactDiv D
      let fs :=
        match C.asConst? with
        | some (-1) => if j % 2 == 1 then fs.flipSign else fs
        | some _ => fs
        | none => factorSqfPp C fs x j
      loop D (B.exactDiv D) fs x (j + 1)

/-- z3 `manager::factor` (:6700). -/
def factorM (p : MPoly) : MFactors :=
  if p.isZero then { constant := 0 }
  else factorCore p {}

/-- z3 `polynomial::cache::factor` view: the DISTINCT factors —
constant and multiplicities dropped. -/
def factorDistinct (p : MPoly) : Array MPoly := (factorM p).factors.map (·.1)

end MPoly

end LeanNonlinearArith.Nlsat
