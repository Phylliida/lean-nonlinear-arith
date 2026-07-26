import LeanNonlinearArith.Kernel.QPoly
import LeanNonlinearArith.Kernel.Mpbq

/-!
# nla-09 (computational half) — root isolation and algebraic sign
determination

Real algebraic numbers for the nlsat lane, represented as
`(polynomial, isolating interval)`: this file provides the *untrusted*
computations — Sturm-bisection isolation into rational-endpoint intervals
and Tarski-query sign determination at an isolated root. The trusted half
(emitting nla-02-style certified claims — IVT isolation witnesses,
sign-from-rootlessness) is a separate design piece; these functions only
produce the candidate data those certificates will pin down.

Invariants maintained (and relied on downstream):
* every emitted isolating interval `(a, b)` has **non-root endpoints** and
  exactly one distinct root of the (internally square-freed) polynomial
  strictly inside — split points are nudged off roots, and the initial
  Cauchy-bound endpoints are outside the root range by construction;
* refinement preserves both properties.
-/

namespace LeanNonlinearArith.Kernel.QPoly

/-- Generalized Sturm chain for the Tarski query: starts `f, f'·g`, then
the usual negated-remainder cascade (elements `|lc|`-normalized as in
`sturmChain`). -/
def sturmChainGen (f g : QPoly) : Array QPoly := Id.run do
  let absNorm (q : QPoly) : QPoly :=
    if q.isEmpty then q else
      let l := lc q
      smul (1 / (if l < 0 then -l else l)) q
  let mut chain : Array QPoly := #[absNorm f]
  let mut a := f
  let mut b := mul (derivative f) g
  for _ in [0:f.size + g.size + 2] do
    if b.isEmpty then return chain
    chain := chain.push (absNorm b)
    let r := neg (rem a b)
    a := b
    b := absNorm r
  return chain

/-- Tarski query `TaQ(g, f; a, b) = Σ_{f(α)=0, a<α<b} sign g(α)` (each
distinct root counted once; requires non-root endpoints). With exactly one
root in the interval this *is* `sign g(α)`. -/
def tarskiQuery (g f : QPoly) (a b : Rat) : Int :=
  let ch := sturmChainGen f g
  (signVarAt ch a : Int) - (signVarAt ch b : Int)

/-- Nudge a proposed split point off the roots of `p`: tries
`m + (b-a)/4^k` for `k = 1, 2, …`. The try count `p.size + 1` is
*provably* sufficient, not heuristic: the candidate points are pairwise
distinct and `p` has at most `deg p` roots, so some candidate is a
non-root. All candidates stay inside `(a, b)` (offsets are `≤ (b-a)/4`). -/
def nonRootSplit (p : QPoly) (a b : Rat) : Rat := Id.run do
  let m := (a + b) / 2
  if eval p m != 0 then return m
  let mut off := (b - a) / 4
  for _ in [0:p.size + 1] do
    let m' := m + off
    if eval p m' != 0 then return m'
    off := off / 4
  return m  -- unreachable by the counting argument above

/-- Isolate the distinct real roots of `p`: returns disjoint open intervals
`(a, b)` with rational non-root endpoints, each containing exactly one real
root of `p`, sorted left to right. Works on the square-free part, so
multiplicities never matter. -/
def isolateRoots (p0 : QPoly) : Array (Rat × Rat) := Id.run do
  let p := squarefreePart p0
  if p.size ≤ 1 then return #[]
  let ch := sturmChain p
  let cnt (a b : Rat) : Nat := signVarAt ch a - signVarAt ch b
  let M := rootBound p
  let mut work : Array (Rat × Rat) := #[(-M, M)]
  let mut out : Array (Rat × Rat) := #[]
  -- runs to completion: bisection of a square-free polynomial terminates
  -- because distinct roots have positive separation, so no fuel — a fuel
  -- cutoff here silently DROPPED unfinished intervals (whole roots missing
  -- from the output with no signal; 2026-07-26 review fix)
  while !work.isEmpty do
    let (a, b) := work.back!
    work := work.pop
    let n := cnt a b
    if n == 0 then continue
    if n == 1 then
      out := out.push (a, b)
    else
      let m := nonRootSplit p a b
      work := work.push (a, m)
      work := work.push (m, b)
  return out.qsort (fun x y => x.1 < y.1)

/-- Halve an isolating interval `iters` times, keeping the root inside and
the endpoints off the roots. -/
def refineInterval (p0 : QPoly) (a b : Rat) (iters : Nat) : Rat × Rat := Id.run do
  let p := squarefreePart p0
  let ch := sturmChain p
  let cnt (x y : Rat) : Nat := signVarAt ch x - signVarAt ch y
  let mut lo := a
  let mut hi := b
  for _ in [0:iters] do
    let m := nonRootSplit p lo hi
    if cnt lo m == 1 then hi := m else lo := m
  return (lo, hi)

/-- Sign of `g` at the algebraic number isolated by `(f, (a, b))`
(exactly one root of `f` in the interval, non-root endpoints):
`-1 / 0 / 1`. The Tarski query with a single root in range collapses to
the sign itself. `f` is square-freed internally to match `isolateRoots`. -/
def signAtRoot (g f : QPoly) (a b : Rat) : Int :=
  tarskiQuery g (squarefreePart f) a b

/-! ## Mpbq-endpoint interface (nla-26.1b; native since the F5/F7 review)

Z3 keeps isolating intervals in binary rationals (`mpbq`); ours now do
too. The engine below runs *natively* on `Mpbq` endpoints — midpoints
are `div2 (add a b)`, `nonRootSplitD` offsets are `div2k (sub b a) 2k` —
so dyadic closure holds **by type**, with no `Rat` round-trip and no
exactness escape hatch. Polynomial evaluations and Sturm counts remain
ℚ-valued internally (`toRat` at the eval boundary is exact). The initial
bound is `⌈rootBound⌉` (an integer, hence dyadic) instead of the
rational Cauchy bound. The isolation *engine* remains Sturm-bisection vs
Z3's Descartes frames — the declared nla-08 engine divergence; what this
interface fixes is the endpoint representation that `am.select` niceness
(nla-26.4) and binary magnitude gating (nla-26.6) read. -/

/-- `nonRootSplit` on dyadic endpoints: `mid + (b−a)/4^k` candidates,
all dyadic by construction; the `p.size + 1` try count is provably
sufficient (pairwise-distinct candidates vs `≤ deg p` roots). -/
def nonRootSplitD (p : QPoly) (a b : Mpbq) : Mpbq := Id.run do
  let m := Mpbq.div2 (Mpbq.add a b)
  if eval p m.toRat != 0 then return m
  let mut off := Mpbq.div2k (Mpbq.sub b a) 2
  for _ in [0:p.size + 1] do
    let m' := Mpbq.add m off
    if eval p m'.toRat != 0 then return m'
    off := Mpbq.div2k off 2
  return m  -- unreachable by the counting argument above

/-- `isolateRoots` with native dyadic endpoints: integer initial bound,
dyadic splits throughout. Isolates the roots of `squarefreePart p0`;
pair the emitted intervals with THAT polynomial (see
`RAlg.isolateRoots`, which does this for you — nla-25/F5). -/
def isolateRootsD (p0 : QPoly) : Array (Mpbq × Mpbq) := Id.run do
  let p := squarefreePart p0
  if p.size ≤ 1 then return #[]
  let ch := sturmChain p
  let cnt (a b : Mpbq) : Nat := signVarAt ch a.toRat - signVarAt ch b.toRat
  let M : Mpbq := Mpbq.ofInt (Mpbq.ratCeilInt (rootBound p))
  let mut work : Array (Mpbq × Mpbq) := #[(Mpbq.neg M, M)]
  let mut out : Array (Mpbq × Mpbq) := #[]
  while !work.isEmpty do
    let (a, b) := work.back!
    work := work.pop
    let n := cnt a b
    if n == 0 then continue
    if n == 1 then
      out := out.push (a, b)
    else
      let m := nonRootSplitD p a b
      work := work.push (a, m)
      work := work.push (m, b)
  return out.qsort (fun x y => Mpbq.lt x.1 y.1)

/-- `signAtRoot` at a dyadic-endpoint isolating interval. -/
def signAtRootD (g f : QPoly) (a b : Mpbq) : Int :=
  signAtRoot g f a.toRat b.toRat

/-- Sign of `p` at a dyadic point. -/
def evalSignAtD (p : QPoly) (x : Mpbq) : Int :=
  let v := eval p x.toRat
  if v < 0 then -1 else if v == 0 then 0 else 1

/-- z3 `upolynomial::refine_core` (nla-26.5): one bisection step on a
*refinable* interval — `p` square-free with opposite nonzero endpoint
signs (`signA = sign p(a) ≠ 0`), which our `RAlg.root` invariant
(exactly one root, simple, non-root endpoints) guarantees. The midpoint
is tested FIRST: a zero midpoint means the actual root was found
(`.inr`), the value-refinement behavior `nonRootSplit` deliberately
dodges — right for isolation, wrong here. Otherwise the half keeping the
sign change survives (`.inl`). -/
def refineCoreStepD (p : QPoly) (signA : Int) (a b : Mpbq) :
    (Mpbq × Mpbq) ⊕ Mpbq :=
  let mid := Mpbq.div2 (Mpbq.add a b)
  let s := evalSignAtD p mid
  if s == 0 then .inr mid
  else if s == signA then .inl (mid, b)
  else .inl (a, mid)

/-- Iterate `refineCoreStepD` `k` times (the loop inside z3
`am::refine(a, k)`), stopping early when the root is found exactly. -/
def refineStepsD (p : QPoly) (signA : Int) (a b : Mpbq) (k : Nat) :
    (Mpbq × Mpbq) ⊕ Mpbq := Id.run do
  let mut lo := a
  let mut hi := b
  for _ in [0:k] do
    match refineCoreStepD p signA lo hi with
    | .inl (lo', hi') => lo := lo'; hi := hi'
    | .inr r => return .inr r
  return .inl (lo, hi)

/-- z3 `upolynomial::refine(…, prec_k)` (what `am::get_interval` runs on
a *copy* of the cell interval): refine until the width is `< 1/2^precK`
— the binary `lt_1div2k` gate — or the root is found exactly. Terminates:
the width halves every step. -/
partial def refineToPrecD (p : QPoly) (signA : Int) (a b : Mpbq)
    (precK : Nat) : (Mpbq × Mpbq) ⊕ Mpbq :=
  if (Mpbq.sub b a).lt1Div2k precK then .inl (a, b)
  else
    match refineCoreStepD p signA a b with
    | .inl (a', b') => refineToPrecD p signA a' b' precK
    | .inr r => .inr r

end LeanNonlinearArith.Kernel.QPoly
