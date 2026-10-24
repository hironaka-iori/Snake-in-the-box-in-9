import CycleExclusion471
import CycleExclusion472
import CycleExclusion473
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.SingletonPatterns
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem exclusion471 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,a,e] : List Nat).getD j 0)
    (hsmall : coreAlpha p (r+4) ≤ 1) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow471.excluded_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    have hjL : j<6 := by simpa [CycleWindow471.directions] using hj
    rw [hd j hjL]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 0 (by simp)
    · exact hs 4 (by simp)

  · intro i hi
    have hiN : i<5 := by simpa [CycleWindow471.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow471.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

theorem lower471 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,a,e] : List Nat).getD j 0) : 2 ≤ coreAlpha p (r+4) := by
  by_contra h
  exact exclusion471 p r a b c d e hn h9 hr hd (by omega)
#print axioms exclusion471
#print axioms lower471

theorem exclusion472 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+7 ≤ m)
    (hd : ∀ j, j<7 → dir p (r+j) = ([a,b,c,d,a,e,b] : List Nat).getD j 0)
    (hsmall : coreAlpha p (r+1) ≤ 1) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow472.excluded_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    have hjL : j<7 := by simpa [CycleWindow472.directions] using hj
    rw [hd j hjL]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 0 (by simp)
    · exact hs 4 (by simp)
    · exact hs 1 (by simp)

  · intro i hi
    have hiN : i<6 := by simpa [CycleWindow472.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow472.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

theorem lower472 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+7 ≤ m)
    (hd : ∀ j, j<7 → dir p (r+j) = ([a,b,c,d,a,e,b] : List Nat).getD j 0) : 2 ≤ coreAlpha p (r+1) := by
  by_contra h
  exact exclusion472 p r a b c d e hn h9 hr hd (by omega)
#print axioms exclusion472
#print axioms lower472

theorem exclusion473 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j<8 → dir p (r+j) = ([a,b,c,d,a,c,e,d] : List Nat).getD j 0)
    (hsmall : coreAlpha p (r+7) ≤ 1) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow473.excluded_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    have hjL : j<8 := by simpa [CycleWindow473.directions] using hj
    rw [hd j hjL]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 0 (by simp)
    · exact hs 2 (by simp)
    · exact hs 4 (by simp)
    · exact hs 3 (by simp)

  · intro i hi
    have hiN : i<7 := by simpa [CycleWindow473.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow473.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

theorem lower473 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j<8 → dir p (r+j) = ([a,b,c,d,a,c,e,d] : List Nat).getD j 0) : 2 ≤ coreAlpha p (r+7) := by
  by_contra h
  exact exclusion473 p r a b c d e hn h9 hr hd (by omega)
#print axioms exclusion473
#print axioms lower473
end Snake9.LocalWindow.SingletonPatterns
