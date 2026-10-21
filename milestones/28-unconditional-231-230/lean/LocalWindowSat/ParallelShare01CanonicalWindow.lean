import LocalWindowSat.ParallelShare01Window
import ParallelShareShapeBridge

/-! The completed pilot on every window with the corresponding canonical shape,
with no coordinate-list or certificate premise. -/
namespace Snake9.LocalWindow.ParallelShare01CanonicalWindow
open WindowAutomaton ParallelShareShapeBridge

theorem share_ge_21 {m : Nat} (p : Snake m) (r : Nat) (hr : r + 7 ≤ m)
    (hshape : canon (blockList p r 7) = ParallelShare01Window.directions) :
    21 ≤ ((List.range 6).map fun i => coreParallelShare p (r + i + 1)).sum := by
  apply refuted_canonical_window p r 7 20 (by decide) hr
  rw [hshape]
  exact ParallelShare01Window.canonical_refuted

#print axioms share_ge_21
end Snake9.LocalWindow.ParallelShare01CanonicalWindow
