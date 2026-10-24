import CycleExclusion401
import CycleExclusion402
import LocalWindowDirBridge
import Mathlib.Tactic

namespace Snake9.LocalWindow.InterveningCounts
set_option maxHeartbeats 0
def directions : List Nat := [0,1,2,3,4,2,0,3]

theorem renamed_exclusion (bs : List (Nat × Nat))
    (h : Refuted CycleWindow401.window bs) (hlen : bs.length = 7)
    {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (hb : ∀ i, i < 7 → (bs.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bs.getD i (0,21)).2) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply refuted_bridge p (mkPerm [a,b,c,d,e]) r (cs := directions) h
    ⟨rfl,rfl,by decide⟩ (by simp [directions,hlen]) hr
  · intro j hj
    have hj8 : j < 8 := by simpa [directions] using hj
    rw [hd j hj8]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 4 (by simp)
    · exact hs 2 (by simp)
    · exact hs 0 (by simp)
    · exact hs 3 (by simp)
  · simpa [hlen] using hb

theorem third_excluded {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) (h3 : coreAlpha p (r+3) ≤ 4)
    (h7 : coreAlpha p (r+7) ≤ 3) : False := by
  apply renamed_exclusion CycleWindow401.bounds CycleWindow401.refuted rfl p r a b c d e hn h9 hr hd
  intro i hi
  have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
  interval_cases i <;> simp only [CycleWindow401.bounds, List.getD_cons_zero,
    List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
    simp_all only [Nat.add_zero]

theorem sixth_excluded {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) (h6 : coreAlpha p (r+6) ≤ 4)
    (h7 : coreAlpha p (r+7) ≤ 3) : False := by
  apply renamed_exclusion CycleWindow402.bounds CycleWindow402.refuted rfl p r a b c d e hn h9 hr hd
  intro i hi
  have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
  interval_cases i <;> simp only [CycleWindow402.bounds, List.getD_cons_zero,
    List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
    simp_all only [Nat.add_zero]

theorem intervening_bounds {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,e,c,a,d] : List Nat).getD j 0)
    (h1 : coreAlpha p (r+1) ≤ 3) (h7 : coreAlpha p (r+7) ≤ 3) :
    5 ≤ coreAlpha p (r+3) ∧ 5 ≤ coreAlpha p (r+6) := by
  constructor
  · by_contra h
    exact third_excluded p r a b c d e hn h9 hr hd h1 (by omega) h7
  · by_contra h
    exact sixth_excluded p r a b c d e hn h9 hr hd h1 (by omega) h7

#print axioms renamed_exclusion
#print axioms third_excluded
#print axioms sixth_excluded
#print axioms intervening_bounds
end Snake9.LocalWindow.InterveningCounts
