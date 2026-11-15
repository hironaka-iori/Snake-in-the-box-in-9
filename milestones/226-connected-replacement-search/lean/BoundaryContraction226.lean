import Std

set_option Elab.async false

namespace BoundaryContraction226

private theorem removed_left {a b i : Nat}
    (inside : a < i ∧ i < b) (outside : ¬(a + 1 < i ∧ i < b)) :
    i = a + 1 := by omega

private theorem removed_right {a b i : Nat}
    (inside : a < i ∧ i < b) (outside : ¬(a < i ∧ i < b - 1)) :
    i = b - 1 := by omega

private theorem contract_first {V : Type} (p q : Nat → V) (n a b c d : Nat)
    (agreement : ∀ i, i ≤ n → ¬(a < i ∧ i < b) →
      ¬(c < i ∧ i < d) → q i = p i)
    (unchanged : q (a + 1) = p (a + 1) ∨ q (b - 1) = p (b - 1)) :
    ∃ a' b', ((a' = a + 1 ∧ b' = b) ∨ (a' = a ∧ b' = b - 1)) ∧
      ∀ i, i ≤ n → ¬(a' < i ∧ i < b') → ¬(c < i ∧ i < d) → q i = p i := by
  rcases unchanged with left_same | right_same
  · refine ⟨a + 1, b, Or.inl ⟨rfl, rfl⟩, ?_⟩
    intro i bound outside_first outside_second
    by_cases inside : a < i ∧ i < b
    · have same_index := removed_left inside outside_first
      simpa only [same_index] using left_same
    · exact agreement i bound inside outside_second
  · refine ⟨a, b - 1, Or.inr ⟨rfl, rfl⟩, ?_⟩
    intro i bound outside_first outside_second
    by_cases inside : a < i ∧ i < b
    · have same_index := removed_right inside outside_first
      simpa only [same_index] using right_same
    · exact agreement i bound inside outside_second

/-- If each replacement retains one boundary-adjacent vertex, the same
candidate agrees outside two intervals shortened by one edge each. -/
theorem contract_two_intervals {V : Type} (p q : Nat → V) (n a b c d : Nat)
    (agreement : ∀ i, i ≤ n → ¬(a < i ∧ i < b) →
      ¬(c < i ∧ i < d) → q i = p i)
    (first_unchanged : q (a + 1) = p (a + 1) ∨ q (b - 1) = p (b - 1))
    (second_unchanged : q (c + 1) = p (c + 1) ∨ q (d - 1) = p (d - 1)) :
    ∃ a' b' c' d',
      ((a' = a + 1 ∧ b' = b) ∨ (a' = a ∧ b' = b - 1)) ∧
      ((c' = c + 1 ∧ d' = d) ∨ (c' = c ∧ d' = d - 1)) ∧
      ∀ i, i ≤ n → ¬(a' < i ∧ i < b') → ¬(c' < i ∧ i < d') → q i = p i := by
  obtain ⟨a', b', first_choice, first_agreement⟩ :=
    contract_first p q n a b c d agreement first_unchanged
  obtain ⟨c', d', second_choice, second_agreement⟩ :=
    contract_first p q n c d a' b'
      (fun i bound outside_second outside_first =>
        first_agreement i bound outside_first outside_second) second_unchanged
  exact ⟨a', b', c', d', first_choice, second_choice,
    fun i bound outside_first outside_second =>
      second_agreement i bound outside_second outside_first⟩

/-- Either contraction keeps a nonempty interval contained in the original
and decreases its edge length by exactly one when the original length is at least two. -/
theorem contracted_interval {a b a' b' : Nat} (width : a + 2 ≤ b)
    (choice : (a' = a + 1 ∧ b' = b) ∨ (a' = a ∧ b' = b - 1)) :
    a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ (b' - a') + 1 = b - a := by
  rcases choice with left | right <;> omega

/-- Conditional on exclusion of the four shortened contexts for this same
candidate, at least one block must change both boundary-adjacent vertices. -/
theorem escape_requires_two_boundary_changes {V : Type}
    (p q : Nat → V) (n a b c d : Nat)
    (agreement : ∀ i, i ≤ n → ¬(a < i ∧ i < b) →
      ¬(c < i ∧ i < d) → q i = p i)
    (shorter_excluded : ∀ a' b' c' d',
      ((a' = a + 1 ∧ b' = b) ∨ (a' = a ∧ b' = b - 1)) →
      ((c' = c + 1 ∧ d' = d) ∨ (c' = c ∧ d' = d - 1)) →
      (∀ i, i ≤ n → ¬(a' < i ∧ i < b') →
        ¬(c' < i ∧ i < d') → q i = p i) → False) :
    (q (a + 1) ≠ p (a + 1) ∧ q (b - 1) ≠ p (b - 1)) ∨
    (q (c + 1) ≠ p (c + 1) ∧ q (d - 1) ≠ p (d - 1)) := by
  classical
  by_cases first : q (a + 1) ≠ p (a + 1) ∧ q (b - 1) ≠ p (b - 1)
  · exact Or.inl first
  · by_cases second : q (c + 1) ≠ p (c + 1) ∧ q (d - 1) ≠ p (d - 1)
    · exact Or.inr second
    · have first_unchanged : q (a + 1) = p (a + 1) ∨ q (b - 1) = p (b - 1) := by
        by_cases left_same : q (a + 1) = p (a + 1)
        · exact Or.inl left_same
        · by_cases right_same : q (b - 1) = p (b - 1)
          · exact Or.inr right_same
          · exact False.elim (first ⟨left_same, right_same⟩)
      have second_unchanged : q (c + 1) = p (c + 1) ∨ q (d - 1) = p (d - 1) := by
        by_cases left_same : q (c + 1) = p (c + 1)
        · exact Or.inl left_same
        · by_cases right_same : q (d - 1) = p (d - 1)
          · exact Or.inr right_same
          · exact False.elim (second ⟨left_same, right_same⟩)
      obtain ⟨a', b', c', d', first_choice, second_choice, contracted⟩ :=
        contract_two_intervals p q n a b c d agreement first_unchanged second_unchanged
      exact False.elim (shorter_excluded a' b' c' d' first_choice second_choice contracted)

#print axioms contract_two_intervals
#print axioms contracted_interval
#print axioms escape_requires_two_boundary_changes
end BoundaryContraction226
