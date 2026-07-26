/-!
# nla-09 (trusted bridge, definitions) — root-fact certificates

**Trusted** definitions of the certificate language and its Bool checkers —
this file and `Certificates/Sound.lean` are the trust boundary of the
nlsat bridge. The kernel (`Kernel/Roots.lean`, `Kernel/CertGen.lean`)
*produces* certificates untrusted; a claim only enters a proof through a
kernel-`decide` of a checker here plus the corresponding soundness theorem.

Design constraints that shaped this file (probed 2026-07-26):

* **No `Rat` anywhere.** Kernel `decide` gets stuck reducing `Rat.add`
  (normalization does not whnf), so every checked condition is arithmetic
  on **unnormalized fractions** `PairQ = Int × Int` — cross-multiplication
  only, no gcd, GMP-fast in the kernel (probe: 60 degree-8 Horner evals
  with growing numerators decide in ~1s).
* Denominator positivity is **checked, never assumed**: `pLt`/`pLe` are
  cross-multiplications that are only meaningful with positive
  denominators, so the checkers test `posDen` on every pair they receive
  (`a`, `b` at the top level, each split point at its node); pair
  *results* built by `pAdd`/`pMul`/… preserve positivity, which the
  soundness file proves once.
* **Integer coefficients.** The certificate is always about a ℤ-coefficient
  polynomial (`List Int`, index = degree); the kernel clears rational
  denominators before emitting a claim (roots and signs are unchanged up
  to the positive scale factor, which the kernel accounts for).
* Two-node certificates: `lip` closes an interval by a Lipschitz margin
  (mean value theorem: a derivative bound times the half-width beaten by
  the center value), `split` subdivides. Compactness makes this complete
  for genuinely root-free closed intervals; no monotonicity node until
  piece counts demand one.

The zero polynomial is representable (`[]` or all-zero lists) and trailing
zeros are harmless — evaluation semantics, not normal forms, carry the
meaning (`derivZ` produces trailing zeros freely).
-/

namespace LeanNonlinearArith.Certificates

/-- Unnormalized rational: `(num, den)`. Only meaningful with `0 < den`,
which checkers verify via `posDen` for every pair taken as *input*;
operations preserve positive denominators. Never reduced — no gcd, so the
kernel can evaluate everything by whnf. -/
abbrev PairQ := Int × Int

@[inline] def posDen (x : PairQ) : Bool := 0 < x.2

def pAdd (x y : PairQ) : PairQ := (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

def pSub (x y : PairQ) : PairQ := (x.1 * y.2 - y.1 * x.2, x.2 * y.2)

def pMul (x y : PairQ) : PairQ := (x.1 * y.1, x.2 * y.2)

/-- `|x|`, assuming `0 < x.2` (checked upstream). -/
def pAbs (x : PairQ) : PairQ := ((x.1.natAbs : Int), x.2)

/-- Cross-multiplied `<`; valid iff both denominators are positive. -/
def pLt (x y : PairQ) : Bool := x.1 * y.2 < y.1 * x.2

/-- Cross-multiplied `≤`; valid iff both denominators are positive. -/
def pLe (x y : PairQ) : Bool := x.1 * y.2 ≤ y.1 * x.2

def pMax (x y : PairQ) : PairQ := if pLe x y then y else x

/-- Midpoint `(x + y) / 2`. -/
def pMid (x y : PairQ) : PairQ := (x.1 * y.2 + y.1 * x.2, 2 * (x.2 * y.2))

/-- `x / 2`. -/
def pHalf (x : PairQ) : PairQ := (x.1, 2 * x.2)

/-! ## Integer coefficient lists (index = degree) -/

/-- Coefficientwise sum, zip-with-padding (structural — the shape
`hasDerivAt_evalZ`'s induction needs). -/
def addZ : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addZ xs ys

/-- Formal derivative, defined by the product-rule recursion for
`p = c + X * q`: `p' = q + X * q'`. Produces trailing zeros — harmless,
evaluation carries the semantics. -/
def derivZ : List Int → List Int
  | [] => []
  | _ :: cs => addZ cs (0 :: derivZ cs)

/-- Coefficientwise absolute value: `evalP (absZ cs)` at a nonnegative
point dominates `|evalZ cs|` on `[-M, M]` (the Lipschitz bound's
ingredient). -/
def absZ (cs : List Int) : List Int := cs.map fun c => (c.natAbs : Int)

/-- Horner evaluation of a ℤ-coefficient polynomial at an unnormalized
rational. Preserves positive denominators. -/
def evalP (cs : List Int) (x : PairQ) : PairQ :=
  cs.foldr (fun c acc => pAdd (c, 1) (pMul x acc)) (0, 1)

/-! ## Certificates -/

/-- Root-freeness certificate for a ℤ-polynomial on a closed interval.

* `lip` — Lipschitz margin: with `m` the midpoint, `M = max |a| |b|`, and
  `B = (absZ p')(M) ≥ sup_{[a,b]} |p'|`, check
  `B * (b - a)/2 < |p(m)|`; the mean value theorem then keeps `p` away
  from zero on all of `[a, b]`.
* `split m l r` — subdivide at `a < m < b` (any rational point works; the
  checker verifies the ordering and `m`'s denominator). -/
inductive Cert
  | lip : Cert
  | split : PairQ → Cert → Cert → Cert
deriving Repr, Inhabited

/-- `checkNoRoot cs a b c = true` (with `0 < a.2`, `0 < b.2`, verified by
callers/wrappers) certifies `evalZ cs x ≠ 0` for all `x ∈ [a, b]`.
Vacuously checkable when `b < a` (the interval is empty). -/
def checkNoRoot (cs : List Int) : PairQ → PairQ → Cert → Bool
  | a, b, .lip =>
    let m := pMid a b
    let M := pMax (pAbs a) (pAbs b)
    let B := evalP (absZ (derivZ cs)) M
    pLt (pMul B (pHalf (pSub b a))) (pAbs (evalP cs m))
  | a, b, .split m l r =>
    posDen m && pLt a m && pLt m b &&
    checkNoRoot cs a m l && checkNoRoot cs m b r

/-- Certifies: `evalZ cs` has **exactly one** root in `[a, b]` (and it lies
in the open interval — the endpoint values are nonzero by the sign
condition). Conditions: positive denominators, `a < b`, a strict sign
change between the endpoints, and root-freeness of the derivative on
`[a, b]` (whence strict monotonicity). -/
def checkUniqueRoot (cs : List Int) (a b : PairQ) (dc : Cert) : Bool :=
  posDen a && posDen b && pLt a b &&
  (evalP cs a).1.sign * (evalP cs b).1.sign == -1 &&
  checkNoRoot (derivZ cs) a b dc

/-- Certifies: `0 < evalZ cs x` for all `x ∈ [a, b]` (root-freeness plus a
positive value at `a`; sign invariance does the rest). Vacuous for
`b < a`. -/
def checkPosOn (cs : List Int) (a b : PairQ) (c : Cert) : Bool :=
  posDen a && posDen b && 0 < (evalP cs a).1 && checkNoRoot cs a b c

/-- Certifies: `evalZ cs x < 0` for all `x ∈ [a, b]`. -/
def checkNegOn (cs : List Int) (a b : PairQ) (c : Cert) : Bool :=
  posDen a && posDen b && (evalP cs a).1 < 0 && checkNoRoot cs a b c

end LeanNonlinearArith.Certificates
