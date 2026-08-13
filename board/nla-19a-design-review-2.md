## nla-19a design review 2 `done` (2026-08-03, post-session-1, Danielle-approved R1–R9)

Method: adversarial re-read of `eval_ineq`/`eval_root`
(`nlsat_evaluator.cpp:403-437`) + full decode of the live x²+y²<0
trace + trusted-layer audit. Atom semantics matches z3 EXACTLY (even
factors forced +1, zero short-circuit); the refutation reads coherently
off the bundles (witnesses ±1, psc disc `4x₀²`, factor `[x₀]`,
trichotomy final); no sorry/admit/external_body/native_decide in the
trusted layer. **Decisions (Danielle, 2026-08-03):**

- **R1 resolution replay comes forward into v0 (was 19b).** Every real
  search backjumps through witness decisions ⇒ multi-bundle
  refutations ALWAYS; no end-to-end acceptance without the glue. The
  glue is propositional (per bundle: learned lemma follows from
  antecedent cids + arith lemma by tauto-grade composition; the DAG
  walk to the empty clause), NOT a z3 trail-scan replay. **19b shrinks
  to pseudoDivision/factorSplit identities.**
- **R2 (kit gap, fixing now):** `rootGeneric` at deg ≤ 2 needs
  root-atom semantics with z3's NO-ROOTS rule (`eval_root` :435-437:
  `i > roots.size()` ⇒ atom false). `rootVal` alone is garbage there.
- **R3 (proving now):** `coeffsOf p y = (p.coeffsIn y).toList` —
  sound-by-matching already; the COVERAGE claim wants the theorem.
- **R4 leafNumeric v0 = glue for ALL deg ≤ 2 univariate leaves**
  (roots have closed forms; every comparison polynomializes — the
  `y²=2 → y≥−2` case is nlinarith). `CertGen` certificates reserved
  for deg ≥ 3 leaves (leafNumeric is degree-generic).
- **R5 cellBound redundancy acknowledged as intentional** (all
  encodings are cell bounds; side determined by k; kept for
  composition ergonomics + z3-structure mirroring).
- **R6 factorSplit steps are ALWAYS safe to ignore (Danielle-approved
  under the z3-parity constraint).** The factored poly never appears
  in any clause literal — only its factors do (as standalone sign
  literals: the zero assumption's ¬EQ is ON the factors; addFactors
  inserts factors into todo). The identity never connects clause
  content ⇒ ignoring loses NO coverage of z3's cases: every learned
  clause is still proved from its own literals. Register updated: v0
  ignores factorSplit (documented sound + complete).
- **R7 pseudoDivision is NOT always safe to ignore** (the simplify
  cluster REWRITES literals; the identity can be the semantic link the
  final derivation needs). v0 ignores the step; derivation may fail
  (sound rejection) → 19b.
- **R8 housekeeping:** Check.lean splits Semantics/Discharge when the
  assembly lands; discharge hypotheses unify on full `MPoly.Canon` at
  the assembly boundary.
- **R9 factorSplit steps can duplicate on repeated cached psc calls**
  (literal dedups via alreadyAdded; steps don't). Idempotent, benign.

