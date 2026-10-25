import CycleExclusion483
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.LowCountCompatibility
set_option maxHeartbeats 0

theorem asymmetric_exclusion {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,c] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) (h5 : coreAlpha p (r+5) ≤ 2) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow483.excluded_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    have hjL : j<6 := by simpa [CycleWindow483.directions] using hj
    rw [hd j hjL]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 4 (by simp)
    · exact hs 2 (by simp)
  · intro i hi
    have hiN : i<5 := by simpa [CycleWindow483.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow483.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

theorem conditional_lower {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,c] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) : 3 ≤ coreAlpha p (r+5) := by
  by_contra h
  exact asymmetric_exclusion p r a b c d e hn h9 hr hd h1 (by omega)
#print axioms asymmetric_exclusion
#print axioms conditional_lower
end Snake9.LocalWindow.LowCountCompatibility
