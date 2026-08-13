## nla-19a progress log (2026-08-03, session 1 of the arc)

**DONE (build green 7603 jobs, 9 commits):** the F1–F5 design-review
decisions are in the 19a entry below. `Nlsat/Trace.lean` (8-shape
language + `rootGeneric` B-tier fallback spelled out, `TraceBundle`,
checker-computed fragment gate, emission grammar DRAFT). Egress (F1):
`Solver.pendingTrace` + `traceBundles` (parallel to clauses) +
`finalRefutation` + F2 extraction seam in `check()` (pre-restoreOrder
snapshot). Resolution markers (F5) at every antecedent. Emission +
discharge + pins for ALL FOUR v0 shapes, per-shape interleaved:
- **linearRoot**: `IneqAtom.Holds` sign semantics + single-factor
  collapses + `linearRoot_discharge` (eval level: the `lin_root_*`
  family; LE/GE remap + negation fold reconstructed per kind).
- **thomQuadratic**: S3 family EXTENDED (Q1): sqrt-characterized
  `quadRoot` + the full point-vs-root dictionary
  (`Templates/Quadratic.lean`); `thom_iff` (master equivalence:
  root comparison ⟺ region formula); `thom_discharge` at the eval
  level (`leadSgn`/`quadRootVal`/`rootVal`, A<0 flip); reconstruction
  bridges (`coeffsOf` checker-side structural extraction +
  `coeffsOf_canon`, `ic_dvd`/`ic_pos`, `managerNormalize`
  sign-transfer, `evalP_discPolyOf`, `evalP_pDiffPolyOf_sign`) with
  coeffsOf↔coeffsIn BY-VALUE pins.
- **cellBound**: thin by design (two-step emission — content is the
  encoding discharge applied forward): `rootVal` deg-1/2 unfolding +
  `cellBound_linear`/`cellBound_thom` wrappers + pins.
- **leafNumeric**: re-pinned as a checker-recomputed MARKER (F3);
  emission in `operator()` when the whole output clause is
  univariate-const in var 0 — VERIFIED LIVE: the x²+y²<0 final bundle
  carries `leafNumeric 0` and its learned clause is the trichotomy
  `x₀<0 ∨ x₀²=0 ∨ x₀>0` (discharge pinned in CheckTests). v0 leaves
  are glue-level; higher-degree leaves → `CertGen` at check time.
- pseudoDivision/factorSplit/resolution emission landed (F5,
  undischarged → 19b).

**Trace shape discovered by dumping the live x²+y²<0 refutation:**
three mid-search bundles (zero assumption `x²≠0`, cell bounds `x₀<0`,
`x₀>0` — each = conflict-clause marker + encoding step + cellBound
step + arith marker) + final bundle (leafNumeric marker + arith marker
+ clause markers). Resolution glue (19b) is the skeleta of these.

**NEXT (Slice E + F/G):** Q1 coverage lemma (grammar → S3 family);
the checker assembly — semantic clause decoding at the F2 seam,
per-bundle proof composition (learned-clause theorem from bundle
steps), the final `Γ ⊢ False` round trip on √2-grade hand goals;
negative probes (corrupted trace rejected). The composition's final
contradiction is linarith/nlinarith glue over the per-step facts
(confirmed by the dump: mid-search bundles are definite-disc/Thom
arguments, the final bundle is trichotomy-grade).

