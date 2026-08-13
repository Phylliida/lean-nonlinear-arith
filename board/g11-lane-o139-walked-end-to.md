## G11 lane `done` + o139 walked END-TO-END (2026-08-11) — the broken-tree session closed out

**What landed:** the previous session's uncommitted/broken G11 work is
finished and green (full build 7612 jobs, ZERO snapshot churn).
`Refute.lean`'s `negRootDeg1Produce` (the negative-side deg-1 root
lane) had ~6 compile errors + three latent runtime bugs; cid 9's arith
member now discharges, and **the o139 refutation walks end-to-end**
(all 6 learned cids + the final bundle — the exact 6-conflict DAG
z3-4.12.5 produces, checked by the kernel).

**The bugs (all in `negRootDeg1Produce`, diagnosed via a scratch repro
with the swallowed `try/catch` temporarily logging):**
1. Parse: the `findSignFact` match missed the `| none` case and had a
   stray `else` (the ~6 compile errors were parse cascades).
2. `Or`'s `getAppFnArgs` is `#[A, B]` — the disjunct-type reads were
   `disjArgs[1]!`/`[2]!` (off-by-one; would panic at runtime). Now
   `[0]!` (accessor-eq LHS) / `[1]!` (the `¬rootCmp` RHS).
3. The `linearNonconst_aux` route was unusable: aux's antecedent is
   `0 < S * evalP acc`, but the transported clause sign fact is
   `0 < evalP acc` — for `S = ±1` these differ (`1 * x` is not defeq
   to `x`). Replaced with the sign-matched
   `linearRootNonconst{Pos,Neg}_discharge` + `Iff.not` route; the
   lemmas' `_hholds : 1 ≤ rootCount` argument comes from
   `rootCount_one_of_deg1_lc_ne` off the sign fact's `lc ≠ 0` — the
   house idiom, same as `rootGenericStepProduce`.
4. `mkCoeFactEq`'s RHS kept the list-get REDEX spelling
   (`evalP ρ cs[1]!` on the quoted list): `proveByRefl`'s refl term
   has the intrinsic type `cs[1]! = cs[1]!`, and an `evalP` of the
   redex stalls the mangle's simp-unfold (the equations only fire on
   cons literals) — the Or's `A = 0` branch then can't meet the
   MPoly-spelled `x0 > 0` sign fact under linarith. Fixed by pinning
   the proof's type with `mkExpectedTypeHint` (RHS = the concrete
   MPoly). This also improves the thom lane's hC2/hC1/hL rewrite
   facts.
5. RED HERRING avoided: `Eq.mp`/`Eq.mpr` are NOT the same direction —
   `Eq.mp (h : α = β) : α → β` (forward), `Eq.mpr (h : α = β) : β →
   α` (BACKWARD). The original `Eq.mpr (congrArg cmpA hAE) hcomp`
   idiom (concrete → accessor) was correct all along; two
   "direction-fix" attempts adding `Eq.symm` broke it before the
   core-library signatures were checked. Lesson recorded: check the
   signature before "fixing" a transport direction.

**Pins (RefuteTests, G11 section):** cid 7 arith member with steps
(closes — the production `rootGeneric` lane through
`linearRootNonconstPos_discharge`, lead sign fact from the clause's
own `⟨3,true⟩`); cid 7 step-free REJECTS (load-bearing: without the
cross-link the rootPair fact is glue-opaque); cid 8 with steps AND
step-free both close (no root facts — steps inert; the eq × bare-var
lift carries it); cid 9 with steps AND step-free both close (the
negRoot lane is step-independent, semantic); cid 9 minus the root
literal REJECTS (the remaining ineq core is satisfiable — the lane's
conversion carries the close). The WalkTests o139 example now builds
(previously rejected at cid 9).

**State of the walk:** o139 is the richest checked real refutation to
date (6 vars, 6 conflicts, 12 clauses, rootGeneric + cellBound +
linearRoot + factorSplit shapes, pure-resolution nodes, all six input
clauses referenced). This satisfies HALF of 19b Slice 3's acceptance
("pd1 AND o139 walked"): o139 ✓, pd1 gated on Slices 1–2
(pseudoDivision grammar + consumption).

**Scratch files:** `scratch_cid9.lean` (the cid-9 repro + probes —
gitignored, KEEP; folded into RefuteTests as the G11 section);
`scratch_g11.lean` gained the cid-7/cid-8 no-step probes (same
disposition).

