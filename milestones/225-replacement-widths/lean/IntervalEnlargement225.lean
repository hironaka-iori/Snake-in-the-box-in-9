import ReplacementIndices225

set_option Elab.async false

namespace IntervalEnlargement225

/-- Agreement outside two open intervals persists when each interval is
enlarged. Inclusion of the closed anchor intervals suffices. -/
theorem agreement_of_enlarged_intervals {V : Type} {n : Nat}
    (p q : Fin (n + 1) → V) (a b c d a' b' c' d' : Nat)
    (contains : a' ≤ a ∧ b ≤ b' ∧ c' ≤ c ∧ d ≤ d')
    (agreement : ∀ i, ¬(a < i.val ∧ i.val < b) →
      ¬(c < i.val ∧ i.val < d) → q i = p i) :
    ∀ i, ¬(a' < i.val ∧ i.val < b') →
      ¬(c' < i.val ∧ i.val < d') → q i = p i := by
  intro i outside_first outside_second
  exact agreement i
    (ReplacementIndices225.outside_enlarged contains.1 contains.2.1 outside_first)
    (ReplacementIndices225.outside_enlarged contains.2.2.1 contains.2.2.2 outside_second)

#print axioms agreement_of_enlarged_intervals
end IntervalEnlargement225
