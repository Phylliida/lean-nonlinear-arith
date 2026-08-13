## nla-28 `done` (2026-07-28) — anum statefulness threading (Danielle, 2026-07-26 review; sequence BEFORE/WITH 12c)

Landed per the confirmed design (DESIGN-endgame §6 Q2): explicit
refined-arg tuple returns at RAlg + refined-set returns at IntervalSet;
the 12c solver store will own the assignment-level threading.

**RAlg level** (`Kernel/RAlg.lean`): `compare`/`compareCore` →
`Ordering × RAlg × RAlg` (all became-basic re-dispatch paths return the
mutated cells, z3 `return compare(a, b)` shape; root-vs-rat dispatch
stays mutation-free per source); `intLt`/`intGt` → `Int × RAlg` (z3
const_cast, algebraic_numbers.cpp:2830/2843); `select` →
`Rat × RAlg × RAlg` (`separate` already returned the pair); `lt`/`le`
thread through `compare`. **NEW `isRational`** — the
`imp::is_rational` port (`algebraic_numbers.cpp:285`): rational-root-
theorem discovery, refine to width `< 1/2^(log2|aₙ|+1)`, candidate
`⌊u·|aₙ|⌋/|aₙ|` becomes basic on a root hit; `restore_if_too_small`
ported (miss with magnitude below `minMagnitude` restores the input
interval; became-basic always sticks); `m_not_rational` cache flag
declared-not-ported (pure recomputation, same answers; factorization is
its only other setter — nla-27). ℚ-coefficient `aₙ` via positive
denominator-clearing (the CertGen scaling pattern; declared QPoly
divergence unchanged). `sign`/`signOfPolyAt`/`magnitude`/
`compareRootRat` verified mutation-free in source, kept pure.

**IntervalSet level** (`Nlsat/IntervalSet.lean`): `cmpLowerLower`/
`cmpUpperUpper`/`cmpUpperLower`/`adjacent` return refined intervals;
`mkUnion` → `(s1', s2', union)` with write-back threading through the
sweep, compression, and the full-check; `pickInComplement` →
`(witness, s')` threading intGt/intLt/lt/select refinement into the
stored endpoints — and the shared-endpoint scan now calls `isRational`
exactly as z3 does, so root-represented rational endpoints are
DISCOVERED and returned basic: **the root-represented-rational
divergence at this spot is dissolved** (it leaves the approved-divergence
register; remaining there: eager-canonical MPoly, Sturm-vs-Descartes,
QPoly ℚ[x] bridge).

**Acceptance pins (all green):** intGt refinement persists in the
returned set (width < 1/2); root-of-x²−4-in-(1,3) shared endpoint picks
`.rat 2` AND the returned set's endpoint became basic; mkUnion's
√3-vs-√2 sweep compare refines both stored endpoints (exact
(3/2, 2)/(1, 3/2) forms pinned); isRational candidate path finds 1/3
(non-dyadic, never a midpoint); restore_if_too_small pinned at
|aₙ| = 65536 (returns the input cell, not the 2⁻¹⁷-refined one).
Full build 7575 jobs green, all pre-existing suites re-green under the
new signatures.

Z3's anum ops MUTATE cells and the refinement persists in solver state
— `compare`/`select`/`separate` take `numeral&`, and `int_gt`/`int_lt`
even `const_cast` (`algebraic_numbers.cpp:2830`) to refine interval-set
endpoints stored behind const pointers. Our pure ports discard that
work, so later magnitude gates and select niceness see WIDER intervals
than Z3 would — a behavioral divergence (witness drift), not just
performance. Design: RAlg ops return their (possibly refined)
arguments; `IntervalSet` endpoint comparisons and `pickInComplement`
thread updated intervals back into the stored set; 12c's assignment map
stores refined cells after every evaluator/compare call. [medium
refactor, touches IntervalSet comparison helpers + mkUnion + 12b-ii/12c
signatures] **Design CONFIRMED 2026-07-26 (DESIGN-endgame §6 Q2):
explicit refined-arg tuple returns at RAlg + solver-state store at 12c.
This is the next item; complete mutation-site list in DESIGN-endgame
§2.1.**

