import CycleExclusion7211
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.FourCount7211
set_option maxHeartbeats 0

theorem exclusion {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+5 ≤ m)
    (hd : ∀ j, j<5 → dir p (r+j) = ([a,b,c,a,d] : List Nat).getD j 0)
    (hb : ∀ i, i<4 →
      (([(0,4),(0,5),(0,2),(0,5)] : List (Nat × Nat)).getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (([(0,4),(0,5),(0,2),(0,5)] : List (Nat × Nat)).getD i (0,21)).2) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow7211.excluded_in_snake p (mkPerm [a,b,c,d]) r hr
  · intro j hj
    have hjL : j<5 := by simpa [CycleWindow7211.directions] using hj
    rw [hd j hjL]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 0 (by simp)
    · exact hs 3 (by simp)
  · intro i hi
    have hiL : i<4 := by simpa [CycleWindow7211.bounds] using hi
    simpa [CycleWindow7211.bounds] using hb i hiL
#print axioms exclusion
end Snake9.LocalWindow.FourCount7211
