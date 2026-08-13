## nla-25 `partial` — L2 kernel correctness upgrades (directives from Danielle, 2026-07-26)

**Status 2026-07-26 eve:** 25.1 resolved-by-removal (the gcd fast test
is gone — nla-26.3's `am::compare` port decides different-poly equality
via Sturm–Tarski `V == 0`; remaining counting trust = nla-10 as
before). 25.3 test pins landed and **caught a real sign bug** — a
`(−1)^{degF·d}` parity factor in `resultantElim` wrong for the
documented `Res_x(f,q)` orientation, invisible in the quadratic lane
(`d = 2` keeps the exponent even), exposed by the first `d = 3` pin and
removed. 25.5 differential test landed (~10k union checks vs the
membership oracle + justification provenance). **25.4 DONE 2026-07-26
(279680c, `Nlsat/TypesOrder.lean`):** `Monomial.cmp` proven a linear
order (refl / eq-iff-list-equality / swap / lt+gt-trans), `Canon`
predicates formalize the Types.lean storage invariants, preservation
proven through `Monomial.mul` and `MPoly.add/neg/sub/smulTerm/mul`;
keystone `cmp_mul_left` (`cmp (mul k m) (mul k n) = cmp m n`, an order
*equality*) via the dense exponent-vector characterization
(`go_eq_dense` + `degreeIn_mul` + `Nat.compare` translation-invariance)
— review correction: z3 does NOT rely on this (products are unsorted
`som_buffer` accumulation, `m_lex_sorted` only ever set by an explicit
`lex_sort`); the theorem discharges OUR eager representation's skipped
re-sort in `smulTerm`. Residual (out
of scope, note for later): `substRat`/`ofQPoly`/`coeffsIn` canonicity
not yet stated. **Still open:** proof-layer items only (25.2 = nla-10,
25.3's semantic layer = nla-11a).

From the fresh-context confidence audit + Danielle's review: fix
correctly AND prove where feasible (documented now, scheduled later —
"none of this needs to happen now… but I do want to fix eventually").
Scale flags are honest estimates.

1. **`RAlg.compareCore` gcd-equality endpoint-roots** — fix by
   `nonRootSplit`-style nudging of `lo`/`hi` off roots of `g` before
   counting; endpoint-root test battery. *Proof (Danielle: "ideally"):*
   layered — the cheap half ("a shared root of both polys inside both
   open isolating intervals ⇒ the numbers are equal") is provable NOW
   from root-uniqueness, no Sturm needed; the counting half ("Sturm says
   ≥ 1 root in the open overlap" is truthful) is nla-10 territory.
   [quick fix + cheap-half proof; counting proof gated on nla-10]
2. **`CertGen.rootFreeOn` Sturm conventions** — *prove* (Danielle:
   "worth trying"). This IS the Sturm correctness theorem = **nla-10
   revival** (AFP Sturm_Sequences as the map; upstream-worthy; a real
   multi-session subproject). Note the pragmatic layer that already
   exists: rootFreeOn is only a fast pre-check — the derivative
   root-freeness it gates gets re-certified by `genNoRoot` +
   `checkNoRoot` anyway, so its correctness affects completeness, not
   soundness. [subproject: nla-10]
3. **`detMPoly` / `resultantElim` correctness** — *proof not just tests*
   (Danielle). Two layers: (a) det-of-Laplace-expansion = spec
   determinant [medium, self-contained]; (b) the semantic property the
   call sites consume — common solutions survive elimination — is
   resultant theory = the **nla-11a orbit** (already boarded as the
   algebra track; this gives it a second consumer). Meanwhile add the
   cube-root ≥ 3×3 test pin (`Res_x(y − x, x³ − 2) = y³ − 2`). [test
   now-ish; proofs medium / nla-11a]
4. **MPoly order property theorems** (Danielle: yes) —
   totality/transitivity/antisymmetry of `Monomial.cmp` + canonical-form
   preservation through `add`/`mul`. Pure list induction. [cheap-medium,
   one session] **DONE 2026-07-26 eve, 279680c — see status above.**
5. **`mkUnion` differential test** (Danielle: yes) — random small sets,
   rational probes vs the "in s1 or s2" membership oracle +
   justification validity. [cheap]

