import LeanNonlinearArith.Nlsat.Types
import LeanNonlinearArith.Kernel.ZPoly

/-!
# nla-12d.1b-i — MPoly arithmetic foundations (z3 `polynomial.cpp` @ **4.12.5**)

Untrusted search-side ops on the canonical `MPoly`, ported 1:1 from the
polynomial manager: monomial division/sqrt, graded-lex extremal terms,
`derivative`, `pw`, integer content (`ic`), exact division (scalar and
the graded-lex-max multivariate reduction), `divides`, the
`pseudo_division_core` family, and the polynomial `sqrt` attempt
(consumed by `factor_2_sqf_pp`).

**Template instantiation:** `pseudo_division_core<Exact_d, Quotient,
ModD>` — `ModD` is always false on the nlsat path (`x2d = nullptr` at
every reachable call site; declared non-port), so the family is two
booleans: `exact_pseudo_remainder` = (true, false), `pseudo_remainder`
= (false, false) [12d.5's], `exact_pseudo_division` = (true, true),
`pseudo_division` = (false, true).

**Termination:** the reduction loops (`exactDiv`/`divides`/`sqrt` —
graded-lex-max strictly decreases) and the pseudo-division loop
(`degree(R, x)` strictly decreases) are `partial`; the termination
arguments are registered with **nla-31**.
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-- z3 `mpzzp_manager` mode flag: `none` = ℤ, `some c` = Zp (balanced
reps via nla-27's `ZpCtx`). z3 shares one polynomial representation
and one set of algorithms between the modes — mirrored here by taking
the mode as a parameter on the numeral-touching ops. -/
abbrev NumMode := Option ZpCtx

namespace NumMode

def norm : NumMode → Int → Int
  | none, a => a
  | some c, a => c.norm a

def add (m : NumMode) (a b : Int) : Int := m.norm (a + b)
def sub (m : NumMode) (a b : Int) : Int := m.norm (a - b)
def mul (m : NumMode) (a b : Int) : Int := m.norm (a * b)
def neg (m : NumMode) (a : Int) : Int := m.norm (-a)

/-- z3 `mpzzp_manager::div`: ℤ exact division (pre: `b | a`); Zp
`a·b⁻¹` (prime field). -/
def div : NumMode → Int → Int → Int
  | none, a, b => a / b
  | some c, a, b => c.mul a (c.inv b)

/-- z3 `mpzzp_manager::divides(a, b)` ("`a | b`"): ℤ mpz divisibility;
Zp prime field ⇒ any nonzero divides. -/
def divides : NumMode → Int → Int → Bool
  | none, a, b => if a == 0 then b == 0 else b % a == 0
  | some _, a, _ => a != 0

/-- z3 `mpzzp_manager::gcd` = mpz gcd in BOTH modes (gcd of the
balanced reps). -/
def gcd (a b : Int) : Int := Int.gcd a b

/-- z3 `m().power`, mode-aware. -/
def pow (m : NumMode) (a : Int) : Nat → Int
  | 0 => m.norm 1
  | k + 1 => m.mul (m.pow a k) a

end NumMode

namespace Monomial

/-- z3 `mm().div(m1, m2, r)`: pointwise exponent subtraction when
`m2 | m1` (ascending-var storage preserved). -/
def div? : Monomial → Monomial → Option Monomial
  | m, [] => some m
  | [], _ :: _ => none
  | (x, e) :: m, (y, f) :: n =>
    if x == y then
      if e ≥ f then
        match div? m n with
        | some r => some (if e == f then r else (x, e - f) :: r)
        | none => none
      else none
    else if x < y then
      match div? m ((y, f) :: n) with
      | some r => some ((x, e) :: r)
      | none => none
    else none

/-- z3 `monomial::is_square`. -/
def isSquare (m : Monomial) : Bool := m.all (·.2 % 2 == 0)

/-- z3 `mm().sqrt`: halve exponents, `none` (z3 nullptr) on odd. -/
def sqrt : Monomial → Option Monomial
  | [] => some []
  | (x, e) :: m =>
    if e % 2 == 1 then none
    else match sqrt m with
      | some r => some ((x, e / 2) :: r)
      | none => none

/-- z3 `mm().div_x_k`: reduce x's exponent by `k` (pre: `k ≤ degreeIn m x`;
dropping the variable at exponent 0). -/
def divXk (m : Monomial) (x : Var) (k : Nat) : Monomial :=
  m.filterMap fun (y, e) =>
    if y == x then (if e - k == 0 then none else some (y, e - k))
    else some (y, e)

/-- z3 `mm().pw`. -/
def pw (m : Monomial) (k : Nat) : Monomial := m.map fun (x, e) => (x, e * k)

end Monomial

namespace MPoly

/-- `x^k` as a polynomial (the unit poly at `k = 0`). -/
def ofVarPow (x : Var) (k : Nat) : MPoly := if k == 0 then ofInt 1 else [(1, [(x, k)])]

/-- Normalize every coefficient through the numeral mode, dropping
zeros (z3's `is_p_normalized` maintenance; identity in ℤ mode). -/
def pNorm (mode : NumMode) (p : MPoly) : MPoly :=
  match mode with
  | none => p
  | some c =>
    p.foldl (fun acc (a, m) =>
      let a' := c.norm a
      if a' == 0 then acc else add acc [(a', m)]) []

/-- Mode-aware arithmetic (z3's manager-mode ops on the shared
representation). In ℤ mode these reduce to the plain ops. -/
def addM (mode : NumMode) (p q : MPoly) : MPoly := pNorm mode (add p q)
def negM (mode : NumMode) (p : MPoly) : MPoly := pNorm mode (neg p)
def subM (mode : NumMode) (p q : MPoly) : MPoly := pNorm mode (sub p q)
def mulM (mode : NumMode) (p q : MPoly) : MPoly := pNorm mode (mul p q)
def smulTermM (mode : NumMode) (a : Int) (mo : Monomial) (p : MPoly) : MPoly :=
  pNorm mode (smulTerm (mode.norm a) mo p)
def pwM (mode : NumMode) (p : MPoly) : Nat → MPoly
  | 0 => ofInt (mode.norm 1)
  | 1 => p
  | k + 2 => mulM mode (pwM mode p (k + 1)) p

/-- z3 `graded_lex_max_pos` as a term (the maximal monomial with its
coefficient). Canonical monomials are unique, so no tie-breaking. -/
def glexMaxTerm : MPoly → Option (Int × Monomial)
  | [] => none
  | (a, m) :: p =>
    some (p.foldl (fun acc (b, n) =>
      if Monomial.gradedLexCompare n acc.2 == .gt then (b, n) else acc) (a, m))

/-- z3 `graded_lex_min_pos` as a term. -/
def glexMinTerm : MPoly → Option (Int × Monomial)
  | [] => none
  | (a, m) :: p =>
    some (p.foldl (fun acc (b, n) =>
      if Monomial.gradedLexCompare n acc.2 == .lt then (b, n) else acc) (a, m))

/-- z3 `derivative(p, x)` (:4554): terms constant in `x` vanish. -/
def derivative (p : MPoly) (x : Var) : MPoly :=
  p.foldl (fun acc (a, m) =>
    let e := m.degreeIn x
    if e == 0 then acc
    else add acc [(a * e, m.divXk x 1)]) []

/-- z3 `pw` (:4643): iterated `mul` (the disabled binary-squaring
`#if 0` is dead upstream). -/
def pw (p : MPoly) : Nat → MPoly
  | 0 => ofInt 1
  | 1 => p
  | k + 2 => mul (pw p (k + 1)) p

/-- z3 `ic(p, a)` (:3386): integer content — the nonneg gcd of all
coefficients (0 for the zero poly), with z3's early exit at 1. -/
def ic (p : MPoly) : Int :=
  match p with
  | [] => 0
  | (a, _) :: rest =>
    rest.foldl (fun acc (b, _) =>
      if acc == 1 then acc else (Int.gcd acc b : Int)) (Int.gcd 0 a : Int)

/-- z3 `ic(p, a, c)` (:3449): content + ℤ-primitive part. Const polys
keep the coeff's SIGN in the content (z3's const branch) — the
non-const branch's gcd is nonneg. Mode-aware scalar division (in Zp
mode `a·inv(g)` equals the integer quotient — `g` divides each rep in
ℤ by the gcd property). -/
def icStrip (p : MPoly) (mode : NumMode := none) : Int × MPoly :=
  match p with
  | [] => (0, [])
  | [(a, [])] => (a, ofInt (mode.norm 1))
  | _ =>
    let a := p.ic
    if a == 1 then (1, p)
    else (a, pNorm mode (p.map fun (b, m) => (mode.div b a, m)))

/-- z3 `exact_div(p, c)` (:5137). Pre: `c ≠ 0` divides every coeff. -/
def exactDivScalar (p : MPoly) (c : Int) (mode : NumMode := none) : MPoly :=
  p.foldl (fun acc (a, m) =>
    let q := mode.div a c
    if q == 0 then acc else add acc [(q, m)]) []

/-- z3 `var_max_degrees` (sorted ascending by var, `power::lt_var`). -/
def varDegrees (p : MPoly) : Array (Var × Nat) := Id.run do
  let mut out : Array (Var × Nat) := #[]
  for (_, m) in p do
    for (x, e) in m do
      match out.findIdx? (·.1 == x) with
      | some i => out := out.set! i (x, max out[i]!.2 e)
      | none => out := out.push (x, e)
  return out.qsort (fun (x, _) (y, _) => x < y)

/-- z3 `get_min_degree_var` (:6433): minimal-degree variable, ties go
to the first in ascending var order (strict `<` keeps the earliest).
`none` for const polys (z3 SASSERTs non-const). -/
def getMinDegreeVar (p : MPoly) : Option Var :=
  (p.varDegrees.foldl (fun acc (x, d) =>
    match acc with
    | none => some (x, d)
    | some (_, dmin) => if d < dmin then some (x, d) else acc) none).map (·.1)

/-- z3 `exact_div(p, q)` (:5159): the graded-lex-max reduction.
Pre: `q | p` (z3 VERIFYs monomial divisibility each step). Mode-aware
coefficient arithmetic (Zp mode: `a·inv(b)` per `mpzzp_manager::div`). -/
partial def exactDiv (p q : MPoly) (mode : NumMode := none) : MPoly := loop p []
where
  loop (R C : MPoly) : MPoly :=
    match R.glexMaxTerm with
    | none => C
    | some (ar, mr) =>
      let (aq, mq) := q.glexMaxTerm.get!
      let mrq := (mr.div? mq).get!
      let arq := mode.div ar aq
      loop (addM mode R (smulTermM mode (-arq) mrq q)) (addM mode C [(arq, mrq)])

/-- z3 `divides(q, p)` (:5197): same sweep, `false` at the first
failed divisibility. Pre: `q ≠ 0`. -/
partial def divides (q p : MPoly) (mode : NumMode := none) : Bool := loop p
where
  loop (R : MPoly) : Bool :=
    match R.glexMaxTerm with
    | none => true
    | some (ar, mr) =>
      let (aq, mq) := q.glexMaxTerm.get!
      match mr.div? mq with
      | none => false
      | some mrq =>
        if !mode.divides aq ar then false
        else loop (addM mode R (smulTermM mode (-(mode.div ar aq)) mrq q))

/-- z3 `pseudo_division_core<exactD, quotient, false>` (:4948).
Returns `(d, Q, R)`; each loop iteration multiplies through by
`lc(q)` once, so `lc(q)^d · p = Q·q + R` with `d` the iteration count
(and `deg_x R < deg_x q` for `q` non-const in `x`). With `exactD`, Q
and R are topped up by `lc(q)^(exact_d − d)` to `exact_d =
deg_A − deg_B + 1` on exit (z3 leaves `d` itself at the iteration
count — both Exact_d call sites discard it).
The `deg_B > deg_A` + `exactD` combination is precondition-excluded
(z3's `SASSERT(d <= exact_d)`; Nat truncated subtraction makes the
top-up a no-op here). `d` is meaningless when `deg_B == 0` and
`quotient = false` (z3 leaves it unset; 0 returned). -/
partial def pseudoDivisionCore (p q : MPoly) (x : Var) (exactD quotient : Bool)
    (mode : NumMode := none) : Nat × MPoly × MPoly :=
  let degA := p.degreeIn x
  let degB := q.degreeIn x
  if degB == 0 then
    if quotient then
      if exactD then
        let d := degA + 1
        if d == 1 then (d, p, [])
        else (d, mulM mode p (pwM mode q (d - 1)), [])
      else (1, p, [])
    else (0, [], [])
  else if degB > degA then (0, [], p)
  else
    let lB := (q.coeffsIn x)[degB]!
    let rB := subM mode q (smulTermM mode 1 [(x, degB)] lB)
    loop degA degB lB rB 0 [] p
where
  loop (degA degB : Nat) (lB rB : MPoly) (d : Nat) (Q R : MPoly) :
      Nat × MPoly × MPoly :=
    let degR := R.degreeIn x
    if degB > degR then
      if exactD then
        let exact_d := degA - degB + 1
        if d < exact_d then
          let lBe := pwM mode lB (exact_d - d)
          (d, if quotient then mulM mode lBe Q else Q, mulM mode lBe R)
        else (d, Q, R)
      else (d, Q, R)
    else
      let step : MPoly × MPoly := Id.run do
        let mut bufR : MPoly := []
        let mut bufQ : MPoly := []
        for (a, m) in R do
          if m.degreeIn x == degR then
            let m' := m.divXk x degB
            if quotient then bufQ := addM mode bufQ [(a, m')]
            bufR := addM mode bufR (smulTermM mode (-a) m' rB)
          else
            bufR := addM mode bufR (smulTermM mode a m lB)
        return (bufR, bufQ)
      let Q' := if quotient then
        Q.foldl (fun acc (a, m) => addM mode acc (smulTermM mode a m lB)) step.2
      else Q
      loop degA degB lB rB (d + 1) Q' step.1

/-- z3 `exact_pseudo_remainder` (:5089): `<true, false>` — the R
component topped up to `exact_d`. -/
def exactPseudoRemainder (p q : MPoly) (x : Var) (mode : NumMode := none) : MPoly :=
  (pseudoDivisionCore p q x true false mode).2.2

/-- z3 `pseudo_remainder` (:5095, release `<false, false>`): iteration-
count `d` + untopped remainder. 12d.5's explain consume. -/
def pseudoRemainder (p q : MPoly) (x : Var) (mode : NumMode := none) : Nat × MPoly :=
  let (d, _, R) := pseudoDivisionCore p q x false false mode
  (d, R)

/-! ## psc chains (`psc_chain_optimized` :5710-5783) -/

/-- Floor log2 (z3's `log2(n)` for `n ≥ 1`) — local, the kernel idiom
(mathlib-free zone). -/
def floorLog2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => 1 + floorLog2 ((n + 2) / 2)
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- z3 `Se_Lazard` (:5618): "Dichotomous Lazard" for the optimized
`S_e`. `lcSd` is `s` (lc of the current `S_d`), `Sd1` the current
`S_{d−1}` poly. -/
partial def SeLazard (d : Nat) (lcSd : MPoly) (Sd1 : MPoly) (x : Var) : MPoly :=
  let e := Sd1.degreeIn x
  let n := d - e - 1
  if n == 0 then Sd1
  else
    let X := (Sd1.coeffsIn x)[e]!
    let a0 := 1 <<< floorLog2 n   -- z3 `1 << log2(n)` (floor)
    let (C, _) := loop X X lcSd a0 (n - a0)
    (mulM none C Sd1).exactDiv lcSd
where
  /-- z3's `while (a != 1) { a /= 2; C = C²/Y; if (n ≥ a)
  { C = C·X/Y; n −= a; } }` with entry `C = X`, `n = n − a0`. -/
  loop (C X Y : MPoly) (a n : Nat) : MPoly × Nat :=
    if a == 1 then (C, n)
    else
      let a' := a / 2
      let C' := (mulM none C C).exactDiv Y
      if n ≥ a' then
        loop ((mulM none C' X).exactDiv Y) X Y a' (n - a')
      else
        loop C' X Y a' n

/-- z3 `optimized_S_e_1` (:5650). -/
partial def optimizedSE1 (d e : Nat) (A Sd1 Se s : MPoly) (x : Var) : MPoly :=
  -- z3 `c_d_1 = lc(S_d_1, x)` — lc at the poly's OWN degree (defective
  -- chains have deg S_{d−1} = e < d−1)
  let c_d_1 := (Sd1.coeffsIn x)[Sd1.degreeIn x]!
  let s_e := (Se.coeffsIn x)[e]!
  -- H_j for j = 0 .. e: s_e·x^j; H_e = s_e·x^e − S_e
  let H0 : Array MPoly := (List.range (e + 1)).toArray.map fun j =>
    if j < e then mulM none (ofVarPow x j) s_e
    else (mulM none (ofVarPow x e) s_e).subM none Se
  -- H_j for j = e+1 .. d-1
  let H : Array MPoly := Id.run do
    let mut H := H0
    for j in [e + 1 : d] do
      let xH := mulM none (ofVarPow x 1) H[j - 1]!
      let xHe := (xH.coeffsIn x)[e]!
      let tmp := (mulM none xHe Sd1).exactDiv c_d_1
      H := H.push (subM none xH tmp)
    return H
  -- D = (Σ coeff(A, j)·H[j]) / lc(A)
  let csA := A.coeffsIn x
  let D0 : MPoly := (List.range d).foldl (fun acc j =>
    addM none acc (mulM none csA[j]! H[j]!)) []
  let D := D0.exactDiv (csA[d]!)
  let xH := mulM none (ofVarPow x 1) H[d - 1]!
  let xHe := mulM none ((xH.coeffsIn x)[e]!) Sd1
  let S1 := (mulM none c_d_1 (addM none xH D)).subM none xHe |>.exactDiv s
  if (d - e + 1) % 2 == 1 then negM none S1 else S1

/-- z3 `psc_chain_optimized_core` (:5710). Pre: `deg P ≥ deg Q > 0`. -/
partial def pscChainCore (P Q : MPoly) (x : Var) : Array MPoly := Id.run do
  let lcQ := (Q.coeffsIn x)[Q.degreeIn x]!
  let s0 := pwM none lcQ (P.degreeIn x - Q.degreeIn x)
  let B0 := P.exactPseudoRemainder (negM none Q) x
  let mut S : Array MPoly := #[]
  let mut A := Q
  let mut B := B0
  let mut s := s0
  while true do
    let d := A.degreeIn x
    let e := B.degreeIn x
    if B.isZero then break
    let ps := (B.coeffsIn x).getD (d - 1) []
    if !ps.isZero then S := S.push ps
    let delta := d - e
    let mut C := B
    if delta > 1 then
      C := SeLazard d s B x
      let ps := (C.coeffsIn x)[e]!
      if !ps.isZero then S := S.push ps
    if e == 0 then break
    B := optimizedSE1 d e A B C s x
    A := C
    s := (A.coeffsIn x)[A.degreeIn x]!
  return S

/-- z3 `psc_chain_optimized` (:5764): the psc chain of `P`, `Q` w.r.t.
`x`, reversed (resultant LAST → first as explain consumes it: z3
reverses so the chain is [psc₀, …]). Empty chain gets a zero (z3
:5772-5773). -/
def pscChain (P Q : MPoly) (x : Var) : Array MPoly :=
  let S :=
    if P.degreeIn x ≥ Q.degreeIn x then pscChainCore P Q x
    else pscChainCore Q P x
  let S := if S.isEmpty then #[MPoly.zero] else S
  S.reverse

/-- z3 `m_manager.is_perfect_square(a, sqrt_a)`: nonneg square root. -/
def isPerfectSquareCoeff (a : Int) : Option Int :=
  if a < 0 then none
  else
    let r := (ZPoly.isqrt a.natAbs : Int)
    if r * r == a then some r else none

/-- z3 `is_perfect_square(p, i, &a)`: monomial square ∧ coeff square. -/
def isPerfectSquareTerm (t : Int × Monomial) : Option Int :=
  if !t.2.isSquare then none else isPerfectSquareCoeff t.1

/-- z3 `sqrt(p, r)` (:5841): the max-monomial-stripping square root
attempt. Both extremal terms must be perfect squares (quick checks);
each step peels `a_i·m_i` with `m_i = m/(2·m₁)`-style division off the
running remainder. `none` when `p` is not a square. -/
partial def sqrt (p : MPoly) : Option MPoly :=
  match p.glexMinTerm, p.glexMaxTerm with
  | none, _ => some []
  | some (amin, mmin), some (amax, mmax) =>
    if !mmin.isSquare || !mmax.isSquare then none
    else match isPerfectSquareCoeff amin, isPerfectSquareCoeff amax with
      | some _, some a =>
        match mmax.sqrt with
        | none => none
        | some m1 =>
          -- C := p without its maximal term
          let C0 := p.filter (·.2 != mmax)
          loop a m1 [(a, m1)] C0
      | _, _ => none
  | _, _ => none
where
  loop (a : Int) (m1 : Monomial) (R C : MPoly) : Option MPoly :=
    match C.glexMaxTerm with
    | none => some R
    | some (ac, mc) =>
      match mc.div? m1 with
      | none => none
      | some mi =>
        let twoa := 2 * a
        if ac % twoa != 0 then none
        else
          let ai := ac / twoa
          let C1 := R.foldl (fun acc (rj, mj) =>
            add acc [(-2 * rj * ai, Monomial.mul mj mi)]) C
          let C2 := add C1 [(-(ai * ai), Monomial.mul mi mi)]
          loop a m1 (add R [(ai, mi)]) C2

end MPoly

end LeanNonlinearArith.Nlsat
