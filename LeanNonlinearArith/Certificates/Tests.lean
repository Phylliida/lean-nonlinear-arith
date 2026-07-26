import LeanNonlinearArith.Certificates.Sound
import LeanNonlinearArith.Kernel.CertGen

/-!
# nla-09 bridge tests

Three layers, mirroring the trust architecture:

* **kernel-`decide` claims** — literal certificates through the trusted
  checkers and their soundness theorems (this is exactly the proof-term
  shape the nla-13/19 trace checker will emit);
* **generator round-trips** — `#guard` (native evaluation) that the
  untrusted synthesis produces certificates the trusted checker accepts
  (`certify*` re-verify internally, so `isSome` is the whole test);
* **negative probes** — claims that are false must not check, whatever
  the certificate.
-/

namespace LeanNonlinearArith.Certificates.Tests

open LeanNonlinearArith.Certificates
open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Kernel.CertGen

/-! ## Trusted claims by kernel `decide` (literal certificates) -/

-- √2: x² − 2 has exactly one root in [1, 2]; the derivative certificate is
-- a bare Lipschitz leaf (2x is far from 0 on [1, 2]).
example : checkUniqueRoot [-2, 0, 1] (1, 1) (2, 1) .lip = true := by decide

example : ∃! x, x ∈ Set.Icc (toR (1, 1)) (toR (2, 1)) ∧ evalZ [-2, 0, 1] x = 0 :=
  checkUniqueRoot_sound (dc := .lip) (by decide)

-- the full ℝ-form massage (the shape the eventual tactic emits): endpoints
-- and polynomial translated to their nominal forms
example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  have h := checkUniqueRoot_sound (cs := [-2, 0, 1]) (a := (1, 1)) (b := (2, 1))
    (dc := .lip) (by decide)
  have e1 : toR ((1 : Int), (1 : Int)) = 1 := by norm_num [toR]
  have e2 : toR ((2 : Int), (1 : Int)) = 2 := by norm_num [toR]
  rw [e1, e2] at h
  have key : ∀ x : ℝ, evalZ [-2, 0, 1] x = x ^ 2 - 2 := by
    intro x
    simp only [evalZ_cons, evalZ_nil]
    push_cast
    ring
  simpa only [key] using h

-- x³ − x − 1 is strictly negative on all of [0, 1] (the real root is
-- ≈ 1.3247): needs one split — the bare leaf's margin fails on the full
-- interval (B·w/2 = 2 vs |p(½)| = 11/8) and holds on both halves.
example : checkNegOn [-1, -1, 0, 1] (0, 1) (1, 1) (.split (1, 2) .lip .lip) = true := by
  decide

example : ∀ x ∈ Set.Icc (toR (0, 1)) (toR (1, 1)), evalZ [-1, -1, 0, 1] x < 0 :=
  checkNegOn_sound (c := .split (1, 2) .lip .lip) (by decide)

-- positivity: x² + 1 on [-3, 3]; the certificate below is the generator's
-- own output (pasted from `#eval certifySignOn #[1, 0, 1] (-3) 3` — pieces
-- must shrink near 0 where |p| bottoms out at 1)
def posOnCert : Cert :=
  .split (0, 1)
    (.split (-3, 2) .lip (.split (-3, 4) .lip .lip))
    (.split (3, 2) (.split (3, 4) .lip .lip) .lip)

example : ∀ x ∈ Set.Icc (toR (-3, 1)) (toR (3, 1)), 0 < evalZ [1, 0, 1] x :=
  checkPosOn_sound (c := posOnCert) (by decide)

/-! ## Negative probes: false claims must not check -/

-- [1, 2] contains √2, so no certificate can certify root-freeness
#guard checkNoRoot [-2, 0, 1] (1, 1) (2, 1) .lip == false
#guard checkNoRoot [-2, 0, 1] (1, 1) (2, 1) (.split (3, 2) .lip .lip) == false
#guard checkNoRoot [-2, 0, 1] (1, 1) (2, 1)
  (.split (3, 2) (.split (5, 4) .lip .lip) (.split (7, 4) .lip .lip)) == false

-- no sign change on [2, 3]: unique-root claim must fail
#guard checkUniqueRoot [-2, 0, 1] (2, 1) (3, 1) .lip == false

-- nonpositive denominators must be rejected (whatever else holds)
#guard checkUniqueRoot [-2, 0, 1] (1, -1) (2, 1) .lip == false
#guard checkNoRoot [-2, 0, 1] (5, 2) (3, 1) (.split (11, -4) .lip .lip) == false

-- p(a) sign gate: checkPosOn on a negative polynomial
#guard checkPosOn [-1, -1, 0, 1] (0, 1) (1, 1) (.split (1, 2) .lip .lip) == false

/-! ## Generator round-trips (native evaluation; `certify*` re-verify
through the trusted checkers before returning `some`) -/

-- root-free interval right of √2
#guard (certifyNoRoot #[-2, 0, 1] 2 3).isSome
-- interval containing √2: must refuse
#guard (certifyNoRoot #[-2, 0, 1] 1 2).isNone
-- sign claims: x³ − x − 1 < 0 on [0, 1]; x² + 1 > 0 on [-3, 3]
#guard (certifySignOn #[-1, -1, 0, 1] 0 1).any fun r => r.2.2.2.2 == false
#guard (certifySignOn #[1, 0, 1] (-3) 3).any fun r => r.2.2.2.2 == true
-- unique root: √2 in (1, 2)
#guard (certifyUniqueRoot #[-2, 0, 1] 1 2).isSome
-- unique root through the square-free path: (x² − 2)² over (1, 2)
#guard (certifyUniqueRoot #[4, 0, -4, 0, 1] 1 2).isSome
-- √3 isolated in (17/10, 9/5) for x⁴ − 5x² + 6 = (x² − 2)(x² − 3);
-- p′ has roots at 0 and ±√(5/2) ≈ ±1.581, outside the interval
#guard (certifyUniqueRoot #[6, 0, -5, 0, 1] (17/10) (9/5)).isSome
-- degenerate: reversed and empty intervals refuse
#guard (certifyNoRoot #[-2, 0, 1] 3 2).isNone

end LeanNonlinearArith.Certificates.Tests
