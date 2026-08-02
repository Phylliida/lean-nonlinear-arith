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
non-const branch's gcd is nonneg. -/
def icStrip (p : MPoly) : Int × MPoly :=
  match p with
  | [] => (0, [])
  | [(a, [])] => (a, ofInt 1)
  | _ =>
    let a := p.ic
    if a == 1 then (1, p)
    else (a, p.map fun (b, m) => (b / a, m))

/-- z3 `exact_div(p, c)` (:5137). Pre: `c ≠ 0` divides every coeff. -/
def exactDivScalar (p : MPoly) (c : Int) : MPoly :=
  p.foldl (fun acc (a, m) =>
    let q := a / c
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
Pre: `q | p` (z3 VERIFYs monomial divisibility each step). -/
partial def exactDiv (p q : MPoly) : MPoly := loop p []
where
  loop (R C : MPoly) : MPoly :=
    match R.glexMaxTerm with
    | none => C
    | some (ar, mr) =>
      let (aq, mq) := q.glexMaxTerm.get!
      let mrq := (mr.div? mq).get!
      let arq := ar / aq
      loop (add R (smulTerm (-arq) mrq q)) (add C [(arq, mrq)])

/-- z3 `divides(q, p)` (:5197): same sweep, `false` at the first
failed divisibility. Pre: `q ≠ 0`. -/
partial def divides (q p : MPoly) : Bool := loop p
where
  loop (R : MPoly) : Bool :=
    match R.glexMaxTerm with
    | none => true
    | some (ar, mr) =>
      let (aq, mq) := q.glexMaxTerm.get!
      match mr.div? mq with
      | none => false
      | some mrq =>
        if ar % aq != 0 then false
        else loop (add R (smulTerm (-(ar / aq)) mrq q))

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
partial def pseudoDivisionCore (p q : MPoly) (x : Var) (exactD quotient : Bool) :
    Nat × MPoly × MPoly :=
  let degA := p.degreeIn x
  let degB := q.degreeIn x
  if degB == 0 then
    if quotient then
      if exactD then
        let d := degA + 1
        if d == 1 then (d, p, [])
        else (d, mul p (pw q (d - 1)), [])
      else (1, p, [])
    else (0, [], [])
  else if degB > degA then (0, [], p)
  else
    let lB := (q.coeffsIn x)[degB]!
    let rB := sub q (smulTerm 1 [(x, degB)] lB)
    loop degA degB lB rB 0 [] p
where
  loop (degA degB : Nat) (lB rB : MPoly) (d : Nat) (Q R : MPoly) :
      Nat × MPoly × MPoly :=
    let degR := R.degreeIn x
    if degB > degR then
      if exactD then
        let exact_d := degA - degB + 1
        if d < exact_d then
          let lBe := pw lB (exact_d - d)
          (d, if quotient then mul lBe Q else Q, mul lBe R)
        else (d, Q, R)
      else (d, Q, R)
    else
      let step : MPoly × MPoly := Id.run do
        let mut bufR : MPoly := []
        let mut bufQ : MPoly := []
        for (a, m) in R do
          if m.degreeIn x == degR then
            let m' := m.divXk x degB
            if quotient then bufQ := add bufQ [(a, m')]
            bufR := add bufR (smulTerm (-a) m' rB)
          else
            bufR := add bufR (smulTerm a m lB)
        return (bufR, bufQ)
      let Q' := if quotient then
        Q.foldl (fun acc (a, m) => add acc (smulTerm a m lB)) step.2
      else Q
      loop degA degB lB rB (d + 1) Q' step.1

/-- z3 `exact_pseudo_remainder` (:5089): `<true, false>` — the R
component topped up to `exact_d`. -/
def exactPseudoRemainder (p q : MPoly) (x : Var) : MPoly :=
  (pseudoDivisionCore p q x true false).2.2

/-- z3 `pseudo_remainder` (:5095, release `<false, false>`): iteration-
count `d` + untopped remainder. 12d.5's explain consume. -/
def pseudoRemainder (p q : MPoly) (x : Var) : Nat × MPoly :=
  let (d, _, R) := pseudoDivisionCore p q x false false
  (d, R)

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
