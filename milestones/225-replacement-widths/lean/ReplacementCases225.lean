import ReplacementIndices225

set_option Elab.async false

namespace ReplacementCases225

theorem classify {a b c d i j : Nat} (blocks : b ≤ c) (indices : i < j) :
    (a ≤ i ∧ j ≤ b) ∨
    (c ≤ i ∧ j ≤ d) ∨
    ((a < i ∧ i < b) ∧ (c < j ∧ j < d) ∧ i + 1 ≠ j) ∨
    ((a < i ∧ i < b) ∧ ¬(a < j ∧ j < b) ∧
      ¬(c < j ∧ j < d) ∧ b < j ∧ i + 1 ≠ j) ∨
    ((c < i ∧ i < d) ∧ ¬(a < j ∧ j < b) ∧
      ¬(c < j ∧ j < d) ∧ d < j ∧ i + 1 ≠ j) ∨
    (¬(a < i ∧ i < b) ∧ ¬(c < i ∧ i < d) ∧
      (a < j ∧ j < b) ∧ i < a ∧ i + 1 ≠ j) ∨
    (¬(a < i ∧ i < b) ∧ ¬(c < i ∧ i < d) ∧
      (c < j ∧ j < d) ∧ i < c ∧ i + 1 ≠ j) ∨
    (¬(a < i ∧ i < b) ∧ ¬(c < i ∧ i < d) ∧
      ¬(a < j ∧ j < b) ∧ ¬(c < j ∧ j < d)) := by
  by_cases first : a ≤ i ∧ j ≤ b
  · exact Or.inl first
  · apply Or.inr
    by_cases second : c ≤ i ∧ j ≤ d
    · exact Or.inl second
    · apply Or.inr
      by_cases hi_first : a < i ∧ i < b
      · by_cases hj_second : c < j ∧ j < d
        · exact Or.inl ⟨hi_first, hj_second,
            ReplacementIndices225.separate_interiors blocks hi_first.2 hj_second.1⟩
        · have h := ReplacementIndices225.after_closed hi_first first
          exact Or.inr (Or.inl ⟨hi_first, h.2.1, hj_second, h.1, h.2.2⟩)
      · apply Or.inr
        apply Or.inr
        by_cases hi_second : c < i ∧ i < d
        · have h := ReplacementIndices225.after_closed hi_second second
          exact Or.inl ⟨hi_second,
            ReplacementIndices225.after_later blocks hi_second.1 indices,
            h.2.1, h.1, h.2.2⟩
        · apply Or.inr
          by_cases hj_first : a < j ∧ j < b
          · have h := ReplacementIndices225.before_closed hj_first first
            exact Or.inl ⟨hi_first, hi_second, hj_first, h.1, h.2⟩
          · apply Or.inr
            by_cases hj_second : c < j ∧ j < d
            · have h := ReplacementIndices225.before_closed hj_second second
              exact Or.inl ⟨hi_first, hi_second, hj_second, h.1, h.2⟩
            · exact Or.inr ⟨hi_first, hi_second, hj_first, hj_second⟩

#print axioms classify
end ReplacementCases225
