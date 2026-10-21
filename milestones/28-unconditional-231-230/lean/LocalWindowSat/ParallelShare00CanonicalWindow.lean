import FastShare00.LocalWindowV2
import ParallelShareApplicability.ParallelShare00
import ParallelShareShapeBridge

/-! Completed Boolean and geometric proofs, on every matching canonical window. -/
namespace Snake9.LocalWindow.ParallelShare00CanonicalWindow
open WindowAutomaton ParallelShareShapeBridge

def directions : List Nat := [0, 1, 2, 0, 3, 1, 0]

theorem canonical_refuted :
    RefutedParallel (winOf directions) (List.replicate 6 (0, 21)) 20 :=
  ParallelShare00Applicability.refuted_of_unsat FastParallelShare00.unsat

theorem share_ge_21 {m : Nat} (p : Snake m) (r : Nat) (hr : r + 7 ≤ m)
    (hshape : canon (blockList p r 7) = directions) :
    21 ≤ ((List.range 6).map fun i => coreParallelShare p (r + i + 1)).sum := by
  apply refuted_canonical_window p r 7 20 (by decide) hr
  rw [hshape]
  exact canonical_refuted

#print axioms canonical_refuted
#print axioms share_ge_21
end Snake9.LocalWindow.ParallelShare00CanonicalWindow
