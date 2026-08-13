## nla-19b Slice 0 `done` (2026-08-10) — simplify-cluster live recon + the o139 search divergence

**Drivers added to scratch_dump.lean** (pd1/pd2/pd3/pd4/pd6; pd5
skipped, pd6 subsumes it). All five refute (`LBool.false`); the one
first-pass surprise (pd3 → `LBool.true`) was DRIVER polarity error on
my side (`1−2x0 < 0` asserted positive means `x0 > 1/2`, not `≤`) —
the solver's verified-model verdict was correct. Lesson for driver
authors: state the target inequality, then double-check the atom
encoding's polarity; verified models make SAT verdicts trustworthy.

**Emission census (live, internal variable order):**

| driver | goal | pseudoDivision payload (f, eq, x, d, r, lcSign, isEven) | rebuilt / lc-atoms | paths |
|---|---|---|---|---|
| pd1 | x1−x0²=0 ∧ x1<0 | (x1, x1−x0², 1, 1, x0², 1, false) | rebuilt ⟨lt,[x0²]⟩ in learned clause | (d) emit+true |
| pd2 | x0≥1 ∧ x0x1−1=0 ∧ x1<0 | (x1, x0x1−1, 1, 1, const 1, 1, false) | empty ⟨lt,[]⟩ atom (never in clauses); A4-GT `x0>0` (atom 5) carries the learned unit | const-drop + A4 |
| pd3 | x0>0 ∧ x0≤1/2 ∧ x0x1²−1=0 ∧ x1²+x1<0 | (1−2v1, v0²v1−1, 1, 1, v0²−2, 1, false) — the BOUND literal rewritten, non-identity reorder | rebuilt ⟨lt,[v0²−2]⟩ + A4-GT (lc = v0², a SQUARE) | (d) + A4 |
| pd4 | x0≤−1 ∧ x0x1−1=0 ∧ x1>0 | (x1, x0x1−1, 1, 1, const 1, −1, false) | empty ⟨lt,[]⟩ + A4-LT `x0<0`; KIND FLIP gt→lt observed in atom 4 creation | const-drop + flip + A4 |
| pd6 | x0≤−1 ∧ x0²≤2 ∧ x0x1−1=0 ∧ 2x1²−1<0 | (2x1²−1, x0x1−1, 1, 2, 2−x0², −1, false) | rebuilt ⟨lt,[2−x0²]⟩ (kind UNFLIPPED — d even), A5-DISEQ fresh atom `x0=0`; EMPTY ⟨gt,[]⟩ also in table | (d) + A5 |

**Structural findings (all grounded in the dumps above):**
- **R-a reorder is live in traces:** pd3's bundle is in internal order
  with a NON-identity permutation (my x0/x1 ↔ v1/v0; eq becomes
  `v0²v1−1` with lc `v0²`). All prior drivers had identity
  permutations — pd3 is the first concrete case where dumps must be
  read modulo reorder (F2 discipline, now witnessed live).
- **R-b path (e) (`normalizeLit`) is UNREACHABLE for in-core
  simplify:** `select_eq` requires `deg(eq, max) > 0` and no core poly
  can exceed `max`, so `info.x = max` always; pseudo-remainders have
  `deg < k` in `info.x`, hence every rebuilt literal drops below max.
  In-core simplify = paths (c)/(d) only. Path (e) exists solely in the
  `select_lower_stage_eq` (x2eq) loop (G5's "vanishing-lc path") —
  **unexercised by any driver; needs exact-hit/lc-vanishing drivers
  (Slice-2 synthetic or future recon).**
- **R-c rewriting targets ANY core literal** (pd3 rewrote the
  x0-BOUND literal, not the "main" ineq) — recon plans that only
  contemplate the interesting atom undercount the shape space.
- **R-d const-remainder drops create EMPTY-FACTOR atoms in the atom
  table** (`⟨.lt,[]⟩` pd2/pd4, `⟨.gt,[]⟩` pd6) that appear in NO
  clause; the A4/A5 lc literals carry the content. Slice 2: atom-table
  snapshots may contain empty atoms; clause literals never reference
  them (observed), the true_literal core-position replacement does
  the dropping.
- **R-e lc-assumption lanes: all four witnessed** — A4-GT (pd2),
  A4-LT (pd4), A4 with lc a perfect square (pd3: `(int v0)² > 0`),
  A5-diseq (pd6: fresh EQ atom `x0 = 0`, d even ⇒ `add_lc_diseq`).
  Plus the lcConst quiet lane: pd6's FINAL bundle contains a var-0
  simplify (`f = x0+1, eq = x0, d=1, r=const 1`) with const lc ⇒ no
  lc assumption emitted.
- **R-f parity quadrant of :1132-1137 witnessed**: (d=1, lcSign=1,
  no flip ×3 drivers), (d=1, lcSign=−1, FLIP — pd4), (d=2, lcSign=−1,
  NO flip — pd6). `isEven=true` payloads and `d ≥ 3` unexercised
  (synthetic-witness territory).
- **R-g simplify runs on stage-0 cores too** (pd6 final bundle:
  var-0 pseudoDivision against a learned unit) — not just
  multi-var-stage conflicts.
- **R-h pd6's second decode detail for Slice 2:** the A5 diseq
  assumption enters proj as `⟨6,false⟩` (the EQ atom unnegated);
  bundle and arith clause semantically check out, but pin the exact
  assumption-literal polarity convention at the F2 seam for EQ-kind
  lc assumptions (Slice 2 item, not a divergence).
- **R-i driver-authoring:** MPoly literals are canonicalized at atom
  creation (input monomial order flexible); dumps display internal
  canonical + reordered forms.

**⚠ MAJOR FINDING — the o139 raw-form search divergence (new item).**
ordering_139 as a raw 6-var real nlsat problem (driver in
gitignored `scratch_o139.lean`): our port searched ≥ 60 min / 5.8 GB
(killed twice, both attempts); **z3 4.16 under the 4.12.5-classic
configuration (`nlsat.lws=false nlsat.randomize=false`, verified the
module in 4.16 is still `nlsat`, `lws`/`randomize` defaults differ
from 4.12.5 exactly as expected) refutes INSTANTLY: 6 conflicts /
11 propagations / 7 stages** — identical counts with lws=true too, so
the classic levelwise distinction is not the cause. Parameter parity
confirmed on our side (factor=true ✓, simplify_cores=true ✓,
reorder=true ✓, randomize=false ✓ both). **Caveat not yet excluded:
z3's SMT front-end preprocessing may prune the problem before nlsat
sees it** (our driver is raw; Verus path feeds preprocessed atoms) —
the divergence might live in input preparation rather than search.
Either way it is SEARCH-side (untrusted layer): soundness untouched,
but parity-directive-relevant and a candidate 12c/explain bug or
input-shape gap. Debugging recipe (next slice on this item): bisect by
variable count to find the smallest multilinear instance showing the
growth; instrument which conflicts repeat (same-core re-derivation ⇒
resolve/backjump; ever-growing new cores ⇒ search-space blowup);
replicate z3's preprocessing to isolate input-shape vs search.
nla-16 would have measured this; recon caught it early.
**Standing-target RESOLVED per the plan's decision rule: the M3
acceptance driver is pd1** (in-fragment, fully quadratic,
pseudoDivision-bearing, multi-bundle DAG — everything the checker
slice needs). ordering_139's fragment status is formally unknowable
until its search completes, but the projection-degree argument
(multilinear inputs, bilinear-by-bilinear resultants ⇒ deg ≤ 2 per
var) says it would be in-fragment; its raw-form search behavior is
the new board item.

**Slice-2 inventory from this recon:** exercised — (d) emit+true,
const-drop w/ empty atoms, A4 both signs + squared lc, A5, lcConst
quiet, reorder. Unexercised: (c) keep-original, (e)/x2eq lower-stage
rewrite loop, isEven=true, d ≥ 3. Synthetic fixtures cover the rest
(fs3FinalBad discipline).

