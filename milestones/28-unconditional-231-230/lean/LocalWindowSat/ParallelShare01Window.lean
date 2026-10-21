import LocalWindowSat.ParallelShare01
import ParallelShareBridge

/-! The first fully certified shape, applied to any matching snake window. -/
namespace Snake9.LocalWindow.ParallelShare01Window

def directions : List Nat := [0, 1, 2, 0, 3, 1, 4]

theorem canonical_refuted :
    RefutedParallel (winOf directions) (List.replicate 6 (0, 21)) 20 :=
  ParallelShare01Certificate.refuted

theorem share_ge_21 {m : Nat} (p : Snake m) (r : Nat) (u : List Nat)
    (hr : r + 7 ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hdir : ∀ j, j < 7 → directions.getD j 0 < u.length ∧
      u.getD (directions.getD j 0) 0 = dir p (r + j)) :
    21 ≤ ((List.range 6).map fun i => coreParallelShare p (r + i + 1)).sum :=
  refuted_parallel_shape (cs := directions) (u := u) canonical_refuted p r
    (by decide) hr hu hu9 hdir

#print axioms canonical_refuted
#print axioms share_ge_21
end Snake9.LocalWindow.ParallelShare01Window
