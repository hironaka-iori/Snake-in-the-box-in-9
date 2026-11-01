import Share7305.Refuted
import LocalWindowShareBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.ShareWindow7305
set_option maxHeartbeats 0
theorem share_bound {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x < 9)
    (hr : r + 6 ≤ m)
    (hd : ∀ j, j < 6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0) :
    12 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have hs := mkPerm_spec hn h9 (by simp)
  have result := refuted_share_bridge p (mkPerm [a,b,c,d]) r refuted
    (cs := [0, 1, 2, 3, 1, 0]) ⟨rfl,rfl,by decide⟩ (by decide) hr
    (by
      intro j hj
      have hj6 : j < 6 := by simpa using hj
      rw [hd j hj6]
      interval_cases j
      · exact hs 0 (by simp)
      · exact hs 1 (by simp)
      · exact hs 2 (by simp)
      · exact hs 3 (by simp)
      · exact hs 1 (by simp)
      · exact hs 0 (by simp)
    )
    (by
      intro i hi
      have hi5 : i < 5 := by simpa [bounds] using hi
      have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
      interval_cases i <;> simpa [bounds] using hu)
  simpa [bounds, cap, resolution] using result
#print axioms share_bound
end Snake9.LocalWindow.ShareWindow7305
