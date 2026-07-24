import Mathlib

/-!
# S1 statement spike (nla-01)

Statement-only formulation of the projection-soundness theorem ("delineability
lite") that the nlsat trace checker rests on. No proofs here — the point is to
force the definitional choices and surface mathlib gaps. See DESIGN.md §3.

Setting: polynomials in a distinguished main variable `y` with coefficients in
`ℝ[x₁..x_k]`, represented as `Polynomial (MvPolynomial (Fin k) ℝ)`. A parameter
point `α : Fin k → ℝ` specializes such a `p` to a univariate real polynomial.

The theorem (S1): if, on a connected parameter set `S`,
  * every `p` in the family keeps its main-variable degree (leading coefficient
    never vanishes on `S`), and
  * every principal subresultant coefficient `psc j p p'` (discriminant chain)
    and `psc j p q` (resultant chain, pairwise) has invariant sign on `S`,
then the family is *delineated* over `S`: there are finitely many continuous,
strictly ordered root functions covering all roots of all family members, with
each member's set of root functions constant across `S`.

This is Collins-style delineability restricted to the psc projection operator
used by Z3's `nlsat_explain.cpp`. Formalized nowhere as of 2026-07.
-/

open Polynomial

namespace LeanNonlinearArith

/-- Polynomials in one main variable over a parameter ring `ℝ[x₁..x_k]`. -/
abbrev ParamPoly (k : ℕ) := Polynomial (MvPolynomial (Fin k) ℝ)

/-- Specialize the parameters at `α`, leaving a univariate real polynomial. -/
noncomputable def evalAt {k : ℕ} (α : Fin k → ℝ) (p : ParamPoly k) : Polynomial ℝ :=
  p.map (MvPolynomial.eval α)

/-!
## Principal subresultant coefficients

`pscMatrix f g j` is the square matrix whose determinant is the `j`-th principal
subresultant coefficient of `f` and `g` (with respect to their `natDegree`s
`m`, `n`): rows are the shifted polynomials `x^(n-j-1)·f, …, f, x^(m-j-1)·g, …, g`
expressed in the monomial basis, columns are the coefficients of degrees
`m+n-j-1` down to `j`. For `j = 0` this is the full Sylvester matrix and the
determinant is the resultant; `psc j f f.derivative` is the discriminant chain.

Natural-number subtraction is total, so the definition is total; the intended
range is `j < min m n` and statements quantify accordingly.
-/

/-- Coefficient of `x^d` in `x^s * h`. -/
def shiftCoeff {R : Type*} [Semiring R] (h : Polynomial R) (s d : ℕ) : R :=
  if s ≤ d then h.coeff (d - s) else 0

/-- The `j`-th subresultant matrix of `f` and `g`. -/
noncomputable def pscMatrix {R : Type*} [CommRing R] (f g : Polynomial R) (j : ℕ) :
    Matrix (Fin (f.natDegree + g.natDegree - 2 * j))
           (Fin (f.natDegree + g.natDegree - 2 * j)) R :=
  Matrix.of fun i c =>
    let m := f.natDegree
    let n := g.natDegree
    let d := m + n - j - 1 - (c : ℕ)      -- column c holds degree-d coefficients
    if (i : ℕ) < n - j then
      shiftCoeff f (n - j - 1 - (i : ℕ)) d
    else
      shiftCoeff g (m - j - 1 - ((i : ℕ) - (n - j))) d

/-- The `j`-th principal subresultant coefficient of `f` and `g`. -/
noncomputable def psc {R : Type*} [CommRing R] (f g : Polynomial R) (j : ℕ) : R :=
  (pscMatrix f g j).det

/-!
## Sign invariance and delineability
-/

/-- A parameter polynomial has invariant sign on `S` (as a function of the
parameters; `0` is a sign). -/
def SignInvariantOn {k : ℕ} (q : MvPolynomial (Fin k) ℝ) (S : Set (Fin k → ℝ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, Real.sign (MvPolynomial.eval α q) = Real.sign (MvPolynomial.eval β q)

/-- A delineation of the family `ps` over the parameter set `S`: finitely many
root functions, continuous on `S`, strictly ordered at every point of `S`,
covering every member's real roots with a membership pattern constant in `α`.
Cells of the nlsat search are the regions between consecutive `θ i`. -/
structure Delineation {k : ℕ} (ps : List (ParamPoly k)) (S : Set (Fin k → ℝ)) where
  /-- Number of root functions. -/
  r : ℕ
  /-- The root functions (values off `S` are irrelevant). -/
  θ : Fin r → (Fin k → ℝ) → ℝ
  continuousOn : ∀ i, ContinuousOn (θ i) S
  ordered : ∀ α ∈ S, StrictMono fun i => θ i α
  /-- Each family member's roots are exactly the values of a fixed subset of
  the root functions — the same subset at every point of `S`. -/
  covers : ∀ p ∈ ps, ∃ I : Finset (Fin r), ∀ α ∈ S,
    (((evalAt α p).roots.toFinset : Finset ℝ) : Set ℝ) = (fun i => θ i α) '' I

/-- Degree invariance on `S`: specialization does not drop the main-variable
degree (equivalently, the leading coefficient does not vanish on `S`). -/
def DegreeInvariantOn {k : ℕ} (p : ParamPoly k) (S : Set (Fin k → ℝ)) : Prop :=
  ∀ α ∈ S, (evalAt α p).natDegree = p.natDegree

/-- **S1, the projection soundness statement.** Sign-invariant psc chains on a
connected set delineate the family. -/
def S1Statement : Prop :=
  ∀ (k : ℕ) (ps : List (ParamPoly k)) (S : Set (Fin k → ℝ)),
    IsPreconnected S →
    (∀ p ∈ ps, p ≠ 0) →
    (∀ p ∈ ps, DegreeInvariantOn p S) →
    -- discriminant chains: p against its main-variable derivative
    (∀ p ∈ ps, ∀ j < p.natDegree, SignInvariantOn (psc p (Polynomial.derivative p) j) S) →
    -- resultant chains: pairwise
    (∀ p ∈ ps, ∀ q ∈ ps, ∀ j < min p.natDegree q.natDegree,
      SignInvariantOn (psc p q j) S) →
    Nonempty (Delineation ps S)

/-!
Downstream corollaries the checker will actually invoke (stated to pin the
interface; provable from `S1Statement` once it is a theorem):

* root-count invariance: `(evalAt α p).roots.toFinset.card` is constant on `S`;
* sign invariance between roots: for a point `y` between `θ i α` and `θ (i+1) α`,
  the sign of `(evalAt α p).eval y` is constant in `α` — the cell-literal
  soundness used by `nlsat_explain.cpp`'s `add_cell_lits`.
-/

/-- Root-count invariance, the first corollary the checker uses. -/
def RootCountCorollary : Prop :=
  ∀ (k : ℕ) (ps : List (ParamPoly k)) (S : Set (Fin k → ℝ)),
    Nonempty (Delineation ps S) →
    ∀ p ∈ ps, ∀ α ∈ S, ∀ β ∈ S,
      (evalAt α p).roots.toFinset.card = (evalAt β p).roots.toFinset.card

end LeanNonlinearArith
