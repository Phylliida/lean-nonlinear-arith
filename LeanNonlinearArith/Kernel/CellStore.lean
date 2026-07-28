import LeanNonlinearArith.Kernel.RAlg

/-!
# Cell store — owner-level sharing for algebraic cells (design 2026-07-28)

z3 has TWO statefulness mechanisms, and they map to two different
mechanisms here:

* **Op level** (`compare`, `int_gt`, `separate`, `is_rational`, …):
  numeral *objects* get refined and handed back. The nla-28 tuple
  returns in `RAlg` are the faithful image of this — and stay exactly
  as they are.
* **Owner level** (`x2v`, interval-set endpoints, `undef_var_assignment`
  sharing, `ext_var2num`, the trail): one cell *shared* by several
  owners, with refinement (and became-basic conversion) visible to all.
  That is what this file provides: a store of cells referenced by id,
  updated **in place** — versioned ids would reintroduce the
  thread-the-update-to-every-owner bug this design exists to kill.

Consequences that come free:

* `undef`/`ext` wrappers: same store, one binding removed/added — the
  nla-28 re-attachment bug class is structurally impossible.
* `save_intervals`: snapshot the few cell *values*, write them back
  where `restore_if_too_small` says so.
* Solver backtracking (12c): one store for the solver's lifetime;
  trail pops remove *bindings*, refinements persist, exactly z3.

`CellM` is `StateM CellStore`; with linear use the array updates
compile to in-place mutation, and `#eval`/`#guard` run it purely.
-/

namespace LeanNonlinearArith.Kernel

/-- The cell heap. Cells ARE `RAlg` values; the store owns nothing else. -/
abbrev CellStore := Array RAlg

/-- Cell reference. Indices are stable for the solver's lifetime. -/
abbrev CellId := Nat

/-- Stateful cell computation (z3's `imp` mutation context). -/
abbrev CellM := StateM CellStore

namespace CellStore

/-- Allocate a fresh cell (z3 `m_wrapper.set` of a new value). Sized
first so the push can reuse the array in place. -/
def fresh (c : RAlg) : CellM CellId := do
  let n := (← get).size
  modify (·.push c)
  return n

/-- Read a cell's current value. -/
def read (i : CellId) : CellM RAlg := do
  return (← get)[i]!

/-- Overwrite a cell in place — every holder of the id sees the update
(z3's shared-cell mutation). -/
def write (i : CellId) (c : RAlg) : CellM Unit := do
  modify fun s => s.set! i c

/-- Update a cell through a pure refinement step. -/
def modifyCell (i : CellId) (f : RAlg → RAlg) : CellM Unit := do
  write i (f (← read i))

/-- Run a computation and discard the store (tests, one-shot queries). -/
def run' (m : CellM α) : α := (m.run #[]).1

/-- Run a computation starting from cells built by `cells`. -/
def runWith (cells : Array RAlg) (m : CellM α) : α := (m.run cells).1

/-! ## Lifted RAlg ops (tuple op in, store write-backs out) -/

/-- z3 `am::compare` on stored cells (refinements persist in place). -/
def compareC (x y : CellId) : CellM Ordering := do
  let a ← read x
  let b ← read y
  let (o, a', b') := RAlg.compare a b
  write x a'
  write y b'
  return o

def ltC (x y : CellId) : CellM Bool := do
  let a ← read x
  let b ← read y
  let (r, a', b') := RAlg.lt a b
  write x a'
  write y b'
  return r

def leC (x y : CellId) : CellM Bool := do
  let a ← read x
  let b ← read y
  let (r, a', b') := RAlg.le a b
  write x a'
  write y b'
  return r

/-- z3 `am::int_lt` (the `const_cast` site). -/
def intLtC (x : CellId) : CellM Int := do
  let a ← read x
  let (r, a') := RAlg.intLt a
  write x a'
  return r

/-- z3 `am::int_gt` (the `const_cast` site). -/
def intGtC (x : CellId) : CellM Int := do
  let a ← read x
  let (r, a') := RAlg.intGt a
  write x a'
  return r

/-- z3 `am::select` on stored cells. Returns the witness as a rational
(z3 sets a basic output numeral) and persists the separated cells. -/
def selectC (x y : CellId) : CellM Rat := do
  let a ← read x
  let b ← read y
  let (w, a', b') := RAlg.select a b
  write x a'
  write y b'
  return w

/-- z3 `am::separate` on stored cells. -/
def separateC (x y : CellId) : CellM Unit := do
  let a ← read x
  let b ← read y
  let (a', b') := RAlg.separate a b
  write x a'
  write y b'

/-- z3 `imp::is_rational` on a stored cell (became-basic persists). -/
def isRationalC (x : CellId) : CellM Bool := do
  let a ← read x
  let (r, a') := RAlg.isRational a
  write x a'
  return r

/-- `refineUntilPrec` on a stored cell. -/
def refineUntilPrecC (x : CellId) (prec : Nat) : CellM Unit := do
  modifyCell x (RAlg.refineUntilPrec · prec)

/-- `refine1` on a stored cell (z3 `am::refine`). -/
def refine1C (x : CellId) : CellM Unit := do
  modifyCell x RAlg.refine1

end CellStore

end LeanNonlinearArith.Kernel
