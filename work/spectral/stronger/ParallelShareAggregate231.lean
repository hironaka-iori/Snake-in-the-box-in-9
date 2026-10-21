import AggregateDirectionK6R34C7WShare231
import ParallelShareShapeBridge
import ParallelShareIdentification

/-! Connect the exact local share family to the existing aggregate's share premise.
No local refutation is assumed to have been completed by the batch here.
-/
namespace Snake9.ParallelShareAggregate231
open LocalWindow ParallelShareShapeBridge ParallelShareIdentification
noncomputable section

theorem shareSeq_eq_core {m : Nat} (p : Snake m) (k : Nat) (hk : k ≤ m) :
    shareSeq p k = coreParallelShare p k := by
  unfold shareSeq
  rw [dif_pos (by omega)]
  exact share_eq_core p ⟨k, by omega⟩

theorem windowShare_eq_core {m : Nat} (p : Snake m) (r : Nat) (hr : r + 7 ≤ m) :
    windowShare p r = ((List.range 6).map fun i => coreParallelShare p (r + i + 1)).sum := by
  unfold windowShare
  rw [shareSeq_eq_core p (r + 1) (by omega), shareSeq_eq_core p (r + 2) (by omega),
    shareSeq_eq_core p (r + 3) (by omega), shareSeq_eq_core p (r + 4) (by omega),
    shareSeq_eq_core p (r + 5) (by omega), shareSeq_eq_core p (r + 6) (by omega)]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
  omega

/-- Exactly the share premise of `upper_231_of_direction_windows_and_shares_all`.
Only the 34 concrete local refutations remain to instantiate this adapter. -/
theorem share_premise_of_family
    (hfamily : ∀ ds ∈ shapes, RefutedParallel (winOf ds) (List.replicate 6 (0, 21)) 20)
    {m : Nat} (p : Snake m) :
    ∀ r, 1 ≤ r → r + 7 ≤ m → 21 ≤ windowShare p r := by
  intro r _ hr
  rw [windowShare_eq_core p r hr]
  exact window_share_ge_21_of_family hfamily p r hr

#print axioms windowShare_eq_core
#print axioms share_premise_of_family
end
end Snake9.ParallelShareAggregate231
