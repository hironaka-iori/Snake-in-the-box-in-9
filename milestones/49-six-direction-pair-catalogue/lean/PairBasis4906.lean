import CycleExclusion4906
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.PairBasis4906
set_option maxHeartbeats 0

theorem exclusion {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 3) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow4906.excluded_in_snake p (mkPerm [a,b,c,d]) r hr
  · intro j hj
    have hjL : j<6 := by simpa [CycleWindow4906.directions] using hj
    rw [hd j hjL]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 0 (by simp)
    · exact hs 3 (by simp)
    · exact hs 2 (by simp)
  · intro i hi
    have hiN : i<5 := by simpa [CycleWindow4906.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow4906.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]
#print axioms exclusion
end Snake9.LocalWindow.PairBasis4906
