import JoinClassification
import Window0
import Window1
import Window2
import Window3
import Mathlib.Tactic

namespace Snake9.ShareJoin
open Snake9.LocalWindow

/-- The classification and four geometric refutations combined. Coordinate
normalization is an explicit hypothesis through P and hP. -/
theorem no_joint_window {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (i : Fin 3) (a b : Fin 8)
    (hr : r + 8 ≤ m)
    (hP : ∀ j, j < 8 → P.fwd (dir p (r+j)) =
      (prefixTypes.getD i.val [] ++ [a.val,b.val]).getD j 0)
    (hj : joint (prefixTypes.getD i.val [] ++ [a.val,b.val]) = true)
    (hcounts : ∀ j, j < 7 → coreAlpha p (r+j+1) = 4) : False := by
  have hc := classified i a b hj
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h
  · apply JointFour0.excluded_in_snake p P r
    · exact hr
    · rw [h] at hP
      exact hP
    · intro j hj
      change j < 7 at hj
      have he := hcounts j hj
      have hb : (JointFour0.bounds.getD j (0,21)) = (4,4) := by
        interval_cases j <;> rfl
      simpa only [hb, he] using (show 4 ≤ 4 ∧ 4 ≤ 4 from ⟨Nat.le_refl 4, Nat.le_refl 4⟩)
  · apply JointFour1.excluded_in_snake p P r
    · exact hr
    · rw [h] at hP
      exact hP
    · intro j hj
      change j < 7 at hj
      have he := hcounts j hj
      have hb : (JointFour1.bounds.getD j (0,21)) = (4,4) := by
        interval_cases j <;> rfl
      simpa only [hb, he] using (show 4 ≤ 4 ∧ 4 ≤ 4 from ⟨Nat.le_refl 4, Nat.le_refl 4⟩)
  · apply JointFour2.excluded_in_snake p P r
    · exact hr
    · rw [h] at hP
      exact hP
    · intro j hj
      change j < 7 at hj
      have he := hcounts j hj
      have hb : (JointFour2.bounds.getD j (0,21)) = (4,4) := by
        interval_cases j <;> rfl
      simpa only [hb, he] using (show 4 ≤ 4 ∧ 4 ≤ 4 from ⟨Nat.le_refl 4, Nat.le_refl 4⟩)
  · apply JointFour3.excluded_in_snake p P r
    · exact hr
    · rw [h] at hP
      exact hP
    · intro j hj
      change j < 7 at hj
      have he := hcounts j hj
      have hb : (JointFour3.bounds.getD j (0,21)) = (4,4) := by
        interval_cases j <;> rfl
      simpa only [hb, he] using (show 4 ≤ 4 ∧ 4 ≤ 4 from ⟨Nat.le_refl 4, Nat.le_refl 4⟩)

#print axioms no_joint_window
end Snake9.ShareJoin
