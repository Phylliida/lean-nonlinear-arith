# HANDOFF — 2026-08-10 (eve; o139 divergence RESOLVED as real port bug;
G11 lane MID-FLIGHT — Refute.lean has ~6 compile errors to finish)

Read first: `DESIGN-endgame.md`, then `BOARD.md` — newest entries:
"nla-19b plan `boarded`" (4 slices), **"nla-19b Slice 0 `done`"**,
**"nla-19b Slice 0 addendum"** (writeback bug analysis). Build system:
Nix `lake` on PATH (not elan); full build was green at 7612 jobs,
commit `d9d5df1`. **Working tree RIGHT NOW: `Refute.lean` FAILS to
build (~6 errors, all in `negRootDeg1Produce`'s new body I just
patched — rerun `lake build LeanNonlinearArith.Nlsat.Refute`, read,
fix; nothing else touched).**

**Source-of-truth rule: all ports cite `git show z3-4.12.5:<path>`
(repo `verus-cad/z3`), never the working tree.** Standing directive
(Danielle): cover ALL cases no matter how rare.

## This session's arc (3 bodies of work, one unfinished)

**1) nla-19b planning + Slice 0 recon (DONE, committed).** 19b plan on
BOARD (4 slices: live recon → grammar+sign-transfer → Refute
consumption → gate lift+acceptance). Decision point 1 RESOLVED with
Danielle: structural-only grammar + per-instance ring-identity
discharge (zeroProductClose idiom, native Q + kernel `ring` close);
d-parity never trusted; cost model recorded (rare-fire, heartbeat-
budgeted). Slice 0: drivers pd1/pd2/pd3/pd4/pd6 added to
`scratch_dump.lean` (all refute); census + R-a..R-i findings on BOARD:
path (e) `normalizeLit` UNREACHABLE for in-core simplify ((c)/(d)
only); reorder live in dumps (read modulo permutation); const-drops
create empty-factor atoms never in clauses; all 4 lc-assumption lanes +
lcConst lane witnessed; parity quadrant witnessed (d odd/lc<0 flip,
d even no-flip). Unexercised: (c) keep-original, x2eq, isEven=true,
d≥3.

**2) o139 search divergence → REAL PORT BUG + fix (DONE, committed
`d9d5df1`).** ordering_139 raw-form hung (>60 min); z3-4.12.5 built
from the audited checkout (worktree `/tmp/z3-4.12.5`, `make -j shell`)
refutes in 28 ms / 6 conflicts / param-parity confirmed. Bisect:
mockExplain → search is fast (17 ms); >280 s inside ONE real
`Explain.explain` call; dbgTrace journal (reverted, never committed)
showed `project`'s todo cycling forever. **Root cause:
`Explain.project`'s in-loop `removeMaxPolys` dropped the state todo
writeback** (z3 mutates `m_todo` in place at
nlsat_explain.cpp:1011; pre-loop call wrote back, in-loop one didn't).
Any projection inserting polys mid-loop (bilinear resultants) cycled.
2-line fix + z3's `m_todo.reset()` on the all_univ break mirrored;
regression pin in `ExplainTests` (o139 end-to-end, `conflicts == 6`);
full build green 7612 ZERO snapshot churn; o139 refutes in ~15–45 ms
with EXACTLY z3's 6 conflicts. First live fidelity bug found by recon;
latent because prior drivers never inserted mid-loop.

**3) Walk o139 end-to-end (IN FLIGHT — this is where we are).** o139's
full refutation is v0 (all bundles isV0, no pseudoDivision/intBranch,
one deg-1 rootGeneric, no S1-gate). Snapshot pasted into
`WalkTests.lean` (`o139Atoms/Clauses/Bundles/Final` + positive example,
goal = all 6 referenced inputs `[[⟨1,true⟩],[⟨2,true⟩],[⟨3,false⟩],
[⟨4,false⟩],[⟨5,false⟩],[⟨6,false⟩]]`, machine-generated). The walk
advanced bundle-by-bundle; **cid 7 closes, cid 8 closes, cid 9 is the
current edge.** What landed en route (all committed? NO — Discharge/
Refute/WalkTests changes are UNCOMMITTED except where noted):

- **G11 = production rootGeneric deg-1 non-const-lc lane** (census's
  "production-unreachable" claim falsified by o139 cid 7).
  Trusted (in `Check/Discharge.lean`, module GREEN):
  `ne_of_one_le_rootCount_deg1`, `linearNonconst_aux` (uniform
  identity `rootCmp k Y (−C/A) ⟺ rootCmp k (S·(A·Y+C)) 0` for
  `S·A > 0`, all 5 kinds), `linearRootNonconst{Pos,Neg}_discharge`,
  `linearRootNonconst_disjunction`, `rootCount_one_of_deg1_lc_ne`,
  `negHolds_deg1_disjunction` (`¬Holds ⟺ (A=0) ∨ ¬rootCmp`).
- Meta (in `Refute.lean`): `rootGenericStepProduce` (positive side;
  sign fact for lead via `findSignFact` → Pos/Neg discharge;
  disjunction fallback) + `.rootGeneric` arm in `collectStepFacts`;
  `extractFacts` negative arm (`negRoot` FactKind, `¬ Holds` fact for
  positive-in-clause root literals) + `negRootFacts` index (tuple is
  now 6-wide) + `negRootDeg1Produce` (negative side: disjunction +
  Or.imp into glue form — accessor bridged concrete, `Iff.not` on aux
  when sign fact present).
- **eq × bare-var lift** (`proveClauseSat`, before sq hints): notes
  `evalP ρ q * ρ v = 0` per eq fact × per clause var — nlinarith can't
  multiply an equality by a free variable (cid-8 lesson); sound via
  congrArg + `zero_mul`.
- Refute-level repros of cid 7 + cid 8 arith members: BOTH CLOSE
  (scratch_g11.lean, gitignored, KEEP — folds into RefuteTests as
  fixtures with load-bearing no-step probes).
- **cid 9 status:** negRoot lane written; the ~6 compile errors I
  patched last (mkFVar on withLocalDecl fvars, getAppFnArgs tuple
  destructure) were theoretical fixes — `lake build
  LeanNonlinearArith.Nlsat.Refute` reported 6 errors remaining when
  context ran out; NOT diagnosed yet, all contained in
  `negRootDeg1Produce`. Then: WalkTests o139 → full build → pins
  (fixture-ize scratch_g11's cid7/cid8 into RefuteTests) → board +
  memory → commit.
- Cid 9's validity argument (for whoever continues): clause
  [⟨3,true⟩,⟨1,false⟩,⟨8,false⟩,⟨7,false⟩]: all-fail ⟹ x0>0,
  x1x3−x0x4 ≤ 0, x0x4−x1x3 ≠ 0 ⟹ x0x4−x1x3 > 0 ⟺ (A = x0 > 0, Pos
  discharge) atom7 HOLDS vs the negRoot literal. The disjunction's
  branch (A=0) dies on the x0>0 sign fact when f0/f2 conversion lands;
  branch ¬cmp needs the Iff.not-aux conversion — both coded, unbuilt.

## Roadmap (unchanged) and where 19b picks up

19b remaining slices (BOARD "plan `boarded`"): **Slice 1** grammar +
trusted pseudo-remainder sign-transfer (per-instance `ring` identity
idiom as in decision 1); **Slice 2** Refute rebuilt-literal
consumption (pd drivers' payloads are the shape space; pd1's own walk
is gated until then); **Slice 3** isV0-gate lift (pseudoDivision only,
intBranch stays) + acceptance = pd1 AND o139 walked. Then 12e (G6) →
14 → 15 → 16; total-to-M6 ~6–10 sessions.

Session mechanics + traps: HANDOFF F3/F4 section (same commit) still
accurate about dump/refresh recipes; NEW traps this session: (1) full
`lean --run` output is BLOCK-BUFFERED when redirected — a
mid-harness hang looks like an earlier driver's hang; flush between
drivers or use separate files. (2) `read_file` tool flaked on
`Check/Semantics.lean` (binary-detect; context work-arounds: sed/grep
or hermes execute_code). (3) `(0:ℝ)` annotation required in Statements
with accessor subterms (the ↑0 cast trap — hit twice). (4) Nothing
matches on `match … | pat | guard =>` — guards are nested `if`s.
(5) z3's `todo_set` in_set is current-contents-only (don't invent
sticky dedup). (6) nlinarith can't multiply an equality by a free
variable — the eq×var lift is the house answer now.

Commits this session: `6d4c887` (Slice 0 + o139 divergence finding),
`d9d5df1` (writeback fix + o139 ExplainTests pin + docs). Uncommitted:
`Check/Discharge.lean` (G11 lemmas, green), `Nlsat/Refute.lean` (G11
lanes + eq×var lift, BUILD BROKEN as noted), `Nlsat/WalkTests.lean`
(o139 snapshot + example; builds only after Refute is green).

Memory file (`verus-cad/memory/project_tactus_nonlinear_port.md`) NOT
updated this session — next session's close should carry: the
writeback-bug story (method: mock bisect → cap timing → dbgTrace
journal → source line-comparison), decision-1 resolution, Slice 0
census facts, G11 lane arc.
