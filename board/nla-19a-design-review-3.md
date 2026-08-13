## nla-19a design review 3 `done` (2026-08-06, mid-F/G arc — parity + regret lenses; R1'/R2' Danielle-approved same day)

Method: adversarial re-read of the day's three landing sites
(Trace.lean grammar finalization, Coverage.lean, Assemble.lean +
the F0 isV0 change) against `git show z3-4.12.5:src/nlsat/
{nlsat_explain,nlsat_solver}.cpp` and the live x0²+x1²<0 dump, with
two explicit lenses: (a) z3 parity, (b) decisions we'd regret.

**VERIFIED CLEAN:**
- **V1 (flush fidelity):** `flushTrace` records
  `clauses[newCid]!.lits` — the SORTED array itself
  (Solver.lean:1055/:1073) — so `bundle.lemma` is byte-identical to
  the learned clause's lits; the walk asserts exact equality by
  `decide`. Sorting is semantically irrelevant anyway: the RUP
  engine is order-insensitive.
- **V2 (unique UNSAT witness):** the empty-lemma exit
  (`finalRefutation`) is the ONLY way UNSAT is witnessed: both
  mkClause sites are guarded by the non-empty check (:1041 precedes
  :1054/:1073), so no empty clause can ever sit in the table for the
  `lemmaIsClause` shortcut (:1066) to match an empty lemma. The
  shortcut path can therefore never steal the refutation (which would
  have been a silent completeness hole — `refutation = none` →
  sound rejection, but a lost proof).
- **V3 (orphan steps):** rounds ending via the lemmaIsClause shortcut
  never flush — their pendingTrace steps self-discard at the next
  round reset (:991), z3's own m_lemma boundary. No cross-round
  leakage into later bundles.
- **V4 (degenerate-path literals all present):** `ensure_sign(q)`
  (:805) and `ensure_sign(A)` (:809) fire BEFORE the `sa == 0`
  reroute (:810), so the disc and A sign literals are always in proj
  when the plinear degenerate runs — `cellBound_plinear`'s `hA0` is
  always sourceable from the clause. Const-zero B then fails plinear
  → generic root atom on the original quadratic; rootCount (A=0,B=0)
  = 0 → atom false by the no-roots rule (R2 machinery covers it).
- **V5 (const-lcFact fix is exact):** the port's `sign c` on a const
  `c` is assignment-independent (evalSignAt evaluates consts) and
  equals `Int.sign` — matches the relaxed grammar condition; const-
  zero lc gives `s = 0` → generic fallback, mirrored by the grammar's
  `s ≠ 0`. The mkNeg pins read off :746/:767 (port :381/:393); the
  `sp` placeholder pin reads off port :415. None of the E1
  tightenings can reject a real emission.
- **V6 (UP engine junk audit):** every junk path fails toward
  rejection (out-of-range bvar = unassignable, fuel exhaustion =
  false, dropped units = smaller closure). Fuel `sz + 1` is exactly
  sufficient: each sweep conflicts, fixpoints, or assigns one NEW
  bvar (unit literals are unassigned by definition), and sz covers
  every bvar in F ∪ target by construction, so the out-of-range
  no-op loop is dead code.

**PARITY NOTES (not divergences):**
- **P-a:** RUP replaces trail-scan replay (R1) and is order-free, so
  the mkClause literal sort, marker order, and duplicate-antecedent
  rounds are all non-issues for the checker.
- **P-b (escape hatch, accepted):** resolution markers carry no
  pivots — UP doesn't need them. If UP ever stalls on a real trace
  (F4 / nla-16 would show it), the fix is to add the pivot bvar to
  the resolution marker payload (the data exists at emit time).
- **P-c:** UP-completeness for the port's resolve chains rests on the
  chain invariant (every antecedent literal lands in the final lemma
  or pivots exactly once). Re-derived the reverse-induction RUP
  argument; it holds for the mark discipline INCLUDING
  `removeLitsFromLvl` (pull-backs re-enter as later pivots).
  Soundness never depends on this — stalls reject.

**REGRET LENSES (decisions):**
- **R1' (APPROVED, lands at F5):** the Nat.cast-0 defaulting means
  Check.lean's discharge hypotheses carry `↑0` forms; every consumer
  must bridge with goal-directed `exact_mod_cast` (today's trap).
  Normalize statements to `(0 : ℝ)` annotations at the F5 split —
  Check.lean is being touched anyway; mechanical and contained.
- **R2' (APPROVED — leave + monitor):** `clauseStatus` does not
  propagate through duplicate unassigned literals (`[l, l]` →
  `.other`). z3's processAntecedent has no dedup in the mark path,
  so duplicates in learned clauses are possible in principle. Stalls
  are sound rejections; nla-16 catches real occurrences. Cheap
  hardening available if ever needed: dedup literals at decode
  (semantically identity).
- **R3' (watch item, no action):** Coverage.lean's theorem shapes are
  unconsumed until F2 — standing rule 3 (shapes validate at
  consumption); adjust Coverage.lean, not the call sites, if F2
  finds a mismatch.
- **R4' (F4 note):** the E1 mkNeg/sp tightenings give new corruption
  surface — F4's negative probes should include a corrupted-mkNeg
  and a corrupted-sp step to confirm parse-level rejection.

**F2 skeleton DONE (2026-08-06 eve).** `Nlsat/Refute.lean` +
`RefuteTests.lean`: the `nlsat_arith_valid` elaborator closes all four
arith lemmas of the live x0²+x1²<0 refutation (bundles 2/3/4/final,
snapshot data embedded literal-form from the reproduced dump) and
rejects an invalid clause (`#guard_msgs (drop error)` probe).
Mechanism: byContradiction → per-literal `¬ litSatI I l` (explicit
∃-motive — HOU-uninferable; `Membership.mem` decide — the instance is
keyed on `Membership.mem`, NOT raw `List.Mem`) → `holds_single_*`
collapses (negated-atom polarity via `Classical.not_not` — supply the
proposition by `mkAppOptM`, mkAppM-with-0-args returns the bare const)
→ `evalP`/`evalM` simp unfold → `sq_nonneg` hints per var → linarith
(R-i workhorse) / nlinarith backup. ALL meta ops that typecheck terms
mentioning context fvars must run inside the CURRENT mvar's
`withContext` (hFvar/h_i leak otherwise — "unknown free variable").
Build green 7608 jobs.

**KERNEL-REDUCTION TRAP (new class, load-bearing for the next
slices):** `Monomial.mul`/`MPoly.add` (and everything built on them:
`MPoly.mul`/`smulTerm`/`sub`) are WF-compiled — they do NOT reduce
under kernel whnf/rfl/decide. Every existing pin passed because
`#guard` evaluates via COMPILATION; kernel defeq was never exercised.
Consequences: (a) atom tables/polys in checker-facing goals must be
LITERAL-LIST form (what nla-14 will quote from the native snapshot
anyway) — never `MPoly`-op consts; (b) **`Monomial.cmp`/`lexCompare`
DO kernel-reduce** (corrected after probing — the WF set is only the
mul family), so `MPoly.Canon` is assemblable in meta: Pairwise via
List lemmas with rfl-grade cmp facts + per-term decides (Canon has NO
Decidable instance — never did); no cmpB bridge needed; (c) `coeffsIn`
reduces only when every degree class is a singleton (multi-term degree
classes hit `MPoly.add` on two non-singletons — e.g. coeff of y² in
x1·y²+x2·y²); (d) decoder reconstructions of WF-built polys (disc =
B²−4AC via `B.mul B`, pDiff, reduct q) must NOT go through kernel
decide — match natively and bridge at the evalP level with the hom
suite (evalP_mul/sub/ofInt + evalP_discPolyOf), which needs no op
reduction; (e) the RUP walk's `upRefutes … by decide` is SAFE
(Nat/Bool only). Grammar-witness conditions (degreeIn equalities,
sign ranges, coeffsIn-singleton facts) are all rfl/decide-grade on
literal polys.

**F2 dump analysis DONE (2026-08-06 eve) — the acceptance-driver
refutation.** The plain √2 goal (`x0 ≥ 0 ∧ x0² ≥ 2 ∧ x0 ≤ 1`) refutes
at STAGE 0 (single `leafNumeric` arith clause — HANDOFF's expectation
that it exercises the discharge chain was WRONG). The real acceptance
driver is the 2-var goal
`x0²+x1² ≥ 2 ∧ x0 ≤ 1 ∧ x1 < 1 ∧ x0 > 0 ∧ x1 > 0` (UNSAT — each
square < 1... plus lower bounds, or it's SAT at negative samples):
refutation = 2 learned bundles + final. Bundle 6: factorSplit ×3 +
linearRoot(gt/lt) + cellBound on x0±1 → arith clause
`¬(x0+1>0) ∨ ¬(x0−1<0) ∨ ¬core` with core
`{⟨5,false⟩, ⟨1,true⟩, ⟨3,false⟩}`. Bundle 7: factorSplit ×3 +
**thomQuadratic(gt,i=1 / lt,i=2) + cellBound** on x0²−2 (sq=1, sa=1,
spd=1, sp=−1) → arith clause with the same core. Final bundle: 3
leafNumeric arith markers (trivially valid) → empty clause.
**Consistency verified end-to-end:** the stored lazy justification
`{⟨5,false⟩, ⟨1,true⟩, ⟨3,false⟩}` matches z3's cover-conflict
construction (R_propagate(~l, tmp, false) over the (−1,1)∪(−∞,0]∪[1,∞)
cover, sections justified by the literals); the core is infeasible at
the interpretation (x0=1: x1>0 ∧ x1²≥1 ∧ x1<1 — the explain contract);
the lazy clause is valid; and the F3 RUP shape checks out by hand
(¬target units ⟨5,true⟩ against input clause 5 = [⟨5,false⟩] →
conflict). Dump recipe (for reproduction): the dump3 setup — init,
2 real vars, atoms lt(x0²+x1²−2), gt(x0−1), lt(x1−1), gt(x0), gt(x1),
unit clauses [¬lt-sum2], [¬gt-xm1], [lt-ym1], [gt-x0], [gt-x1],
`check (resolve Explain.explain)`, print `s.refutation`.
**Phantom-bug lesson (cost ~2h):** a misread `neg` field in one marker
literal (read `⟨5,false⟩` as `⟨5,true⟩`) made the arith clause decode
as standalone-invalid and launched a full semantics audit of
justification polarity (which is CORRECT — verified against z3's
R_propagate/cover construction + an instrumented search replica).
When a decode makes z3 look unsound, re-verify the decode against the
raw dump BEFORE auditing semantics.
**Also confirmed this slice:** `MPoly.Canon` has no Decidable instance
(lemma-assembled: Pairwise via List lemmas + rfl-grade cmp facts +
per-term decides — cmp DOES kernel-reduce; the WF set is only the
mul family).

