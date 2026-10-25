import CycleExclusion4930
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.PairBasis4930
set_option maxHeartbeats 0

theorem exclusion {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,f] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+2) ≤ 2) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow4930.excluded_in_snake p (mkPerm [a,b,c,d,e,f]) r hr
  · intro j hj
    have hjL : j<6 := by simpa [CycleWindow4930.directions] using hj
    rw [hd j hjL]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 4 (by simp)
    · exact hs 5 (by simp)
  · intro i hi
    have hiN : i<5 := by simpa [CycleWindow4930.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow4930.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]
#print axioms exclusion
end Snake9.LocalWindow.PairBasis4930
