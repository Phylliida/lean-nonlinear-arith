import LeanNonlinearArith.Kernel.QPoly
import LeanNonlinearArith.Kernel.Roots
import LeanNonlinearArith.Certificates.Defs

/-!
# nla-09 (trusted bridge, generation) — certificate synthesis (untrusted)

Produces `Certificates.Cert` values for the trusted checkers from the ℚ[x]
kernel's data. Everything here is **untrusted**: a wrong answer can only
make a checker return `false` (or a `decide` fail), never certify a false
claim — the `certify*` functions even re-run the trusted Bool checker
before returning, so `isSome` implies the claim will `decide`.

Pipeline per claim:
1. scale the ℚ-coefficient polynomial to ℤ coefficients (positive lcm of
   denominators — roots and signs on intervals are unchanged);
2. synthesize a `Cert` by refine-until-margin: try the Lipschitz leaf,
   else bisect at the midpoint (compactness terminates this on genuinely
   root-free closed intervals; fuel bounds the recursion defensively);
3. for unique-root claims, first shrink the isolating interval (kernel
   Sturm counts) until the derivative is root-free on the *closed*
   interval — guaranteed reachable because the polynomial is square-freed,
   so the isolated root is simple.

The Rat-arithmetic margin test here mirrors `checkNoRoot`'s pair
arithmetic exactly (both are exact rational arithmetic), so generation
and checking agree.
-/

namespace LeanNonlinearArith.Kernel.CertGen

open LeanNonlinearArith.Kernel.QPoly
open LeanNonlinearArith.Certificates

/-- Exact `Rat → PairQ`; `Rat.den` is positive by invariant. -/
def ratToPair (q : Rat) : PairQ := (q.num, (q.den : Int))

def rabs (q : Rat) : Rat := if q < 0 then -q else q

/-- Scale to integer coefficients (times the positive lcm of denominators);
returns the coefficient list, index = degree. -/
def toIntCoeffs (p : QPoly) : List Int :=
  let d : Nat := p.foldl (fun acc c => Nat.lcm acc c.den) 1
  (p.map fun c => c.num * ((d / c.den : Nat) : Int)).toList

/-- Rebuild a `QPoly` from an integer coefficient list (for reusing the
Sturm machinery on lists like `derivZ cs`). -/
def ofIntCoeffs (cs : List Int) : QPoly :=
  QPoly.trim ⟨cs.map fun c => Rat.ofInt c⟩

/-- Rat-arithmetic evaluation of an integer coefficient list. -/
def evalIntAt (cs : List Int) (x : Rat) : Rat :=
  cs.foldr (fun c acc => Rat.ofInt c + x * acc) 0

/-- `p` has no root anywhere on the **closed** interval `[a, b]`:
non-root endpoints plus a zero Sturm count on the open interval
(square-freed internally; `cnt a b` counts roots in `(a, b]`, which with a
non-root `b` is the open count). -/
def rootFreeOn (p : QPoly) (a b : Rat) : Bool :=
  let sq := squarefreePart p
  if sq.isEmpty then false
  else
    let ch := sturmChain sq
    eval sq a != 0 && eval sq b != 0 && (signVarAt ch a - signVarAt ch b == 0)

/-- Mirror of `checkNoRoot _ _ _ .lip`'s margin condition, in `Rat`. -/
def lipOk (cs : List Int) (a b : Rat) : Bool :=
  let m := (a + b) / 2
  let M := max (rabs a) (rabs b)
  let B := evalIntAt (absZ (derivZ cs)) M
  B * ((b - a) / 2) < rabs (evalIntAt cs m)

/-- Refine-until-margin synthesis: Lipschitz leaf if the margin already
holds, else bisect. Fuel bounds the depth (each level halves the width;
compactness guarantees success at finite depth on root-free closed
intervals). -/
def genNoRoot (cs : List Int) (a b : Rat) : Nat → Option Cert
  | 0 => none
  | fuel + 1 =>
    if lipOk cs a b then some .lip
    else
      let m := (a + b) / 2
      match genNoRoot cs a m fuel, genNoRoot cs m b fuel with
      | some l, some r => some (.split (ratToPair m) l r)
      | _, _ => none

/-- Certify root-freeness of `p` on `[a, b]`. Returns the claim data
`(cs, pa, pb, cert)` for `checkNoRoot`, **already re-verified** through
the trusted checker (so `isSome` ⇒ the `decide` succeeds). -/
def certifyNoRoot (p : QPoly) (a b : Rat) (fuel : Nat := 48) :
    Option (List Int × PairQ × PairQ × Cert) := do
  guard (a < b)
  guard (rootFreeOn p a b)
  let cs := toIntCoeffs p
  let cert ← genNoRoot cs a b fuel
  let pa := ratToPair a
  let pb := ratToPair b
  guard (checkNoRoot cs pa pb cert)
  return (cs, pa, pb, cert)

/-- Certify a strict sign for `p` on all of `[a, b]`: `(claim, isPos)`
with the checker re-run (`checkPosOn` / `checkNegOn` according to the
sign at `a`). -/
def certifySignOn (p : QPoly) (a b : Rat) (fuel : Nat := 48) :
    Option (List Int × PairQ × PairQ × Cert × Bool) := do
  let (cs, pa, pb, cert) ← certifyNoRoot p a b fuel
  let isPos := 0 < evalIntAt cs a
  guard (if isPos then checkPosOn cs pa pb cert else checkNegOn cs pa pb cert)
  return (cs, pa, pb, cert, isPos)

/-- Certify that `p` has exactly one root in the isolating interval
`(a₀, b₀)` (as produced by `isolateRoots` on the square-free part).
Shrinks the interval until the derivative of the square-freed, ℤ-scaled
polynomial is root-free on the closed interval (reachable: the root is
simple), then emits the claim for `checkUniqueRoot` — re-verified.
Returns `(cs, pa, pb, dc)`; the isolated root is the unique root of the
**square-free part**, whose real roots agree with `p`'s. -/
def certifyUniqueRoot (p : QPoly) (a0 b0 : Rat)
    (fuel : Nat := 48) (refineFuel : Nat := 64) :
    Option (List Int × PairQ × PairQ × Cert) := do
  let sp := squarefreePart p
  let cs := toIntCoeffs sp
  let d := ofIntCoeffs (derivZ cs)
  -- shrink until the derivative is root-free on the closed interval
  let mut a := a0
  let mut b := b0
  let mut ok := rootFreeOn d a b
  for _ in [0:refineFuel] do
    if ok then break
    let (a', b') := refineInterval sp a b 1
    a := a'
    b := b'
    ok := rootFreeOn d a b
  guard ok
  let dc ← genNoRoot (derivZ cs) a b fuel
  let pa := ratToPair a
  let pb := ratToPair b
  guard (checkUniqueRoot cs pa pb dc)
  return (cs, pa, pb, dc)

end LeanNonlinearArith.Kernel.CertGen
