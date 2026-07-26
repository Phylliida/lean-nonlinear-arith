import LeanNonlinearArith.Kernel.QPoly

/-!
# nla-12a — nlsat core types (port of `nlsat_types.h`)

Untrusted search-side data. Fidelity notes:

* **Literals** are ported as `(bvar, neg)` pairs (Z3's `sat::literal`
  index = `2·bvar + neg` is kept as a derived function for hashing/tests).
* **Atoms** mirror Z3 exactly: `ineq_atom` = sign condition on a
  *product* of polynomials each tagged with its exponent parity (only
  parity matters for sign semantics); `root_atom` = `x ⋈ rootᵢ(p)` with
  1-based root index. Atom-to-boolean-variable mapping lives in the
  solver's atom table (nla-12c), not here.
* **Polynomials** are sparse multivariate over ℤ (`MPoly`, nla-26.2 —
  matching Z3's `mpz`-coefficient manager): terms `(coeff, monomial)`
  with monomials as strictly-increasing `(var, exp)` lists, exactly
  Z3's ascending-var `power` arrays. Rationals enter only through the
  denominator-clearing substitution (`substRat`, the `substitute`
  positive-scaling trick) and the ℤ-scaled `ofQPoly` embedding — the
  invariant that lets interval evaluation stay exact over dyadics.
  Canonical form: nonzero coeffs, monomials strictly descending in
  `Monomial.cmp` = z3 `lex_compare` (the manager's only sorted storage
  form, `m_lex_sorted`); leading-monomial selection in Z3 is a
  `graded_lex_compare` max-scan, storage-order-independent, ported as
  `gradedLexCompare`.

The evaluator's algebraic-substitution machinery is nla-12b; here only
rational substitution and the univariate view (both needed everywhere)
are provided.
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

abbrev Var := Nat

/-- Monomial: strictly increasing variable indices, positive exponents.
`[]` is the unit monomial. -/
abbrev Monomial := List (Var × Nat)

namespace Monomial

def degreeIn (m : Monomial) (x : Var) : Nat :=
  match m.find? (·.1 == x) with
  | some (_, e) => e
  | none => 0

def totalDegree (m : Monomial) : Nat := m.foldl (fun acc (_, e) => acc + e) 0

/-- Merge-multiply two sorted monomials (exponents add). -/
def mul : Monomial → Monomial → Monomial
  | [], n => n
  | m, [] => m
  | (x, e) :: m, (y, f) :: n =>
    if x < y then (x, e) :: mul m ((y, f) :: n)
    else if y < x then (y, f) :: mul ((x, e) :: m) n
    else (x, e + f) :: mul m n

/-- z3 `lex_compare` (`polynomial.cpp:625`): lexicographic with the
**biggest variable dominating** — `x₃³ > x₃²x₁² > x₃x₂²x₁ > x₁³`.
Z3 compares power arrays from the last position; our ascending-var
lists match that representation, so we walk the reversals. -/
def lexCompare (m n : Monomial) : Ordering := go m.reverse n.reverse
where
  go : Monomial → Monomial → Ordering
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | (x, e) :: m, (y, f) :: n =>
      if x == y then
        if e == f then go m n
        else if e < f then .lt else .gt
      else if x > y then .gt
      else .lt

/-- z3 `graded_lex_compare` (`polynomial.cpp:710`): total degree first,
ties broken by `lexCompare`. The order Z3 selects leading monomials by
(always via max-scan, so storage order never matters to it). -/
def gradedLexCompare (m n : Monomial) : Ordering :=
  match Ord.compare m.totalDegree n.totalDegree with
  | .eq => lexCompare m n
  | o => o

/-- Canonical storage order = z3 `lex_compare` (nla-26.2). Z3 sorts
lazily (`m_lex_sorted`); our persistent lists keep it eagerly. -/
def cmp (m n : Monomial) : Ordering := lexCompare m n

/-- Remove variable `x` from the monomial (used by the univariate view). -/
def erase (m : Monomial) (x : Var) : Monomial := m.filter (·.1 != x)

end Monomial

/-- Sparse multivariate polynomial over ℤ (nla-26.2, z3 `mpz` manager).
Canonical: nonzero coeffs, monomials strictly descending in
`Monomial.cmp` (= z3 lex). -/
abbrev MPoly := List (Int × Monomial)

namespace MPoly

def zero : MPoly := []

def isZero (p : MPoly) : Bool := p.isEmpty

def ofInt (n : Int) : MPoly := if n == 0 then [] else [(n, [])]

def ofVar (x : Var) : MPoly := [(1, [(x, 1)])]

/-- Canonicalizing merge-add of two canonical polynomials. -/
def add : MPoly → MPoly → MPoly
  | [], q => q
  | p, [] => p
  | (a, m) :: p, (b, n) :: q =>
    match Monomial.cmp m n with
    | .gt => (a, m) :: add p ((b, n) :: q)
    | .lt => (b, n) :: add ((a, m) :: p) q
    | .eq =>
      let c := a + b
      if c == 0 then add p q else (c, m) :: add p q

def neg (p : MPoly) : MPoly := p.map fun (a, m) => (-a, m)

def sub (p q : MPoly) : MPoly := add p (neg q)

def smulTerm (c : Int) (mo : Monomial) (p : MPoly) : MPoly :=
  if c == 0 then [] else p.map fun (a, m) => (c * a, Monomial.mul mo m)

def mul (p q : MPoly) : MPoly :=
  p.foldl (fun acc (a, m) => add acc (smulTerm a m q)) []

/-- Largest variable index occurring (the "max var" that stages key on);
`none` for constants. -/
def maxVar (p : MPoly) : Option Var :=
  p.foldl (fun acc (_, m) => m.foldl (fun acc (x, _) => max acc (some x)) acc) none

def degreeIn (p : MPoly) (x : Var) : Nat :=
  p.foldl (fun acc (_, m) => max acc (m.degreeIn x)) 0

/-- View as univariate in `x`: array of coefficient polynomials, index =
degree in `x`. -/
def coeffsIn (p : MPoly) (x : Var) : Array MPoly := Id.run do
  let d := p.degreeIn x
  let mut out : Array MPoly := Array.replicate (d + 1) []
  for (a, m) in p do
    let e := m.degreeIn x
    out := out.set! e (add out[e]! [(a, m.erase x)])
  return out

/-- Substitute a rational `v = n/d` for variable `x`, ℤ-faithfully:
returns `d^{deg_x p} · p[x := v]` — Z3's `substitute` clears
denominators by exactly this positive scaling, which is why rational
values never force rational coefficients (and downstream, why interval
evaluation stays exact over dyadics). All consumers are sign/root
semantics, unchanged by a positive constant factor. -/
def substRat (p : MPoly) (x : Var) (v : Rat) : MPoly := Id.run do
  let dTop := p.degreeIn x
  let mut out : MPoly := []
  for (a, m) in p do
    let e := m.degreeIn x
    let c := a * v.num ^ e * ((v.den : Int)) ^ (dTop - e)
    out := add out [(c, m.erase x)]
  return out

/-- Fully rational-evaluate (all variables assigned; unassigned vars
evaluate at 0 — callers ensure coverage). -/
def evalRat (p : MPoly) (σ : Var → Rat) : Rat :=
  p.foldl (fun acc (a, m) =>
    acc + (a : Rat) * m.foldl (fun acc (x, e) => acc * σ x ^ e) 1) 0

/-- Constant-view: `some n` iff the polynomial is the constant `n`. -/
def asConst? : MPoly → Option Int
  | [] => some 0
  | [(a, [])] => some a
  | _ => none

/-- To kernel `QPoly`, when univariate in `x` with constant coefficients
(the stage-1 shape). `none` if other variables remain. -/
def toQPoly? (p : MPoly) (x : Var) : Option QPoly := Id.run do
  let cs := p.coeffsIn x
  let mut out : Array Rat := Array.replicate cs.size 0
  for i in [0:cs.size] do
    match cs[i]!.asConst? with
    | some c => out := out.set! i (c : Rat)
    | none => return none
  return some (QPoly.trim out)

/-- Embed a kernel `QPoly` (ℚ coefficients) as an ℤ-coefficient `MPoly`
univariate in `x`, scaled by the positive lcm of the denominators
(root- and sign-preserving; the kernel's ℚ[x] representation is the
declared divergence from Z3's ℤ `upolynomial`, bridged here). -/
def ofQPoly (q : QPoly) (x : Var) : MPoly := Id.run do
  let mut l : Nat := 1
  for i in [0:q.size] do
    l := Nat.lcm l (q.coeff i).den
  let mut out : MPoly := []
  for i in [0:q.size] do
    let c := q.coeff i * (l : Rat)   -- integer-valued by construction
    if c != 0 then
      out := add out [(c.num, if i == 0 then [] else [(x, i)])]
  return out

end MPoly

/-! ## Atoms, literals, clauses (`nlsat_types.h`) -/

/-- `ineq_atom` kinds (Z3 `atom::kind`, values `EQ/LT/GT`). -/
inductive IneqKind | eq | lt | gt
deriving Repr, DecidableEq, Inhabited

/-- `root_atom` kinds (`ROOT_EQ/LT/GT/LE/GE`). -/
inductive RootKind | eq | lt | gt | le | ge
deriving Repr, DecidableEq, Inhabited

/-- Sign condition on a product of polynomials; each factor carries its
exponent-parity bit (`isEven`), which is all sign semantics needs.
Z3: `ineq_atom`. -/
structure IneqAtom where
  kind : IneqKind
  factors : List (MPoly × Bool)  -- (factor, isEven)
deriving Repr, Inhabited

/-- `x ⋈ rootᵢ(p)` with 1-based root index `i` (roots of `p` as a
univariate in `x` under the values of lower variables). Z3: `root_atom`. -/
structure RootAtom where
  kind : RootKind
  x : Var
  i : Nat
  p : MPoly
deriving Repr, Inhabited

inductive Atom
  | ineq (a : IneqAtom)
  | root (a : RootAtom)
deriving Repr, Inhabited

namespace Atom

/-- The stage a literal belongs to: max variable of the atom
(`atom::max_var`). -/
def maxVar : Atom → Option Var
  | .ineq a => a.factors.foldl (fun acc (p, _) => max acc (p.maxVar)) none
  | .root a => max (some a.x) (a.p.maxVar)

end Atom

/-- Boolean literal over the solver's atom table (`sat::literal`). -/
structure Literal where
  bvar : Nat
  neg : Bool
deriving Repr, DecidableEq, Inhabited

namespace Literal

/-- Z3's literal index encoding (`2·var + sign`), kept for parity in
displays/hashes. -/
def index (l : Literal) : Nat := 2 * l.bvar + (if l.neg then 1 else 0)

def negate (l : Literal) : Literal := ⟨l.bvar, !l.neg⟩

end Literal

/-- Clause: literal array plus provenance (learned vs input). Justifies
intervals and conflicts; the solver's clause table assigns ids. -/
structure Clause where
  lits : Array Literal
  learned : Bool
deriving Repr, Inhabited

end LeanNonlinearArith.Nlsat
