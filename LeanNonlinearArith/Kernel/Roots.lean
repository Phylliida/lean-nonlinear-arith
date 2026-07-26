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

/-! ## Mpbq-endpoint interface (nla-26.1b)

Z3 keeps isolating intervals in binary rationals (`mpbq`); ours now do
too. The bisection engine above is *dyadic-closed* — midpoints are
`div2 (a + b)` and `nonRootSplit` offsets are `(b − a)/4^k` — so seeding
it with dyadic values keeps every emitted endpoint dyadic, and these
variants share the engine rather than duplicating it: they run it on
`toRat` images and convert the (exactly representable) results back with
`ofRatExact`. The one genuine change is the initial bound: `⌈rootBound⌉`
(an integer, hence dyadic) instead of the rational Cauchy bound. The
isolation *engine* remains Sturm-bisection vs Z3's Descartes frames —
that is the declared nla-08 engine divergence, unchanged here; what this
interface fixes is the endpoint representation that `am.select` niceness
(nla-26.4) and binary magnitude gating (nla-26.6) read. -/

/-- `isolateRoots` with dyadic endpoints: integer initial bound, dyadic
splits throughout. -/
def isolateRootsD (p0 : QPoly) : Array (Mpbq × Mpbq) := Id.run do
  let p := squarefreePart p0
  if p.size ≤ 1 then return #[]
  let ch := sturmChain p
  let cnt (a b : Rat) : Nat := signVarAt ch a - signVarAt ch b
  let M : Rat := (Mpbq.ratCeilInt (rootBound p) : Int)
  let mut work : Array (Rat × Rat) := #[(-M, M)]
  let mut out : Array (Mpbq × Mpbq) := #[]
  while !work.isEmpty do
    let (a, b) := work.back!
    work := work.pop
    let n := cnt a b
    if n == 0 then continue
    if n == 1 then
      out := out.push (Mpbq.ofRatExact a, Mpbq.ofRatExact b)
    else
      let m := nonRootSplit p a b
      work := work.push (a, m)
      work := work.push (m, b)
  return out.qsort (fun x y => Mpbq.lt x.1 y.1)

/-- `refineInterval` on dyadic endpoints (dyadic-closed, see above). -/
def refineIntervalD (p0 : QPoly) (a b : Mpbq) (iters : Nat) :
    Mpbq × Mpbq :=
  let (a', b') := refineInterval p0 a.toRat b.toRat iters
  (Mpbq.ofRatExact a', Mpbq.ofRatExact b')

/-- `signAtRoot` at a dyadic-endpoint isolating interval. -/
def signAtRootD (g f : QPoly) (a b : Mpbq) : Int :=
  signAtRoot g f a.toRat b.toRat

end LeanNonlinearArith.Kernel.QPoly
