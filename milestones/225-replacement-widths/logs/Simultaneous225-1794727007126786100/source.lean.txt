import LayerJoining
import ReplacementIndices225

set_option Elab.async false

namespace Simultaneous225
open LayerJoining

/-- Construct a path from two local replacements. No inducedness or
injectivity of the complete candidate map is assumed. -/
def replaceTwoBlocks {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (q : Fin (n + 1) → V) (a b c d : Nat)
    (ordered : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ n)
    (agreement : ∀ i, ¬(a < i.val ∧ i.val < b) →
      ¬(c < i.val ∧ i.val < d) → q i = p.vertex i)
    (first_distinct : ∀ i j, a ≤ i.val → i.val ≤ b →
      a ≤ j.val → j.val ≤ b → q i = q j → i = j)
    (first_induced : ∀ i j, a ≤ i.val → j.val ≤ b → i.val < j.val →
      (R (q i) (q j) ↔ i.val + 1 = j.val))
    (second_distinct : ∀ i j, c ≤ i.val → i.val ≤ d →
      c ≤ j.val → j.val ≤ d → q i = q j → i = j)
    (second_induced : ∀ i j, c ≤ i.val → j.val ≤ d → i.val < j.val →
      (R (q i) (q j) ↔ i.val + 1 = j.val))
    (first_separated : ∀ i j, (a < i.val ∧ i.val < b) →
      ¬(c < j.val ∧ j.val < d) → (j.val < a ∨ b < j.val) →
      q i ≠ p.vertex j ∧ ¬R (q i) (p.vertex j) ∧ ¬R (p.vertex j) (q i))
    (second_separated : ∀ i j, (c < i.val ∧ i.val < d) →
      ¬(a < j.val ∧ j.val < b) → (j.val < c ∨ d < j.val) →
      q i ≠ p.vertex j ∧ ¬R (q i) (p.vertex j) ∧ ¬R (p.vertex j) (q i))
    (mutual : ∀ i j, (a < i.val ∧ i.val < b) →
      (c < j.val ∧ j.val < d) → q i ≠ q j ∧ ¬R (q i) (q j)) :
    InducedPath V R n := by
  have blocks_order := ordered.2.1
  have pair : ∀ i j : Fin (n + 1), i.val < j.val →
      q i ≠ q j ∧ (R (q i) (q j) ↔ i.val + 1 = j.val) := by
    intro i j index_order
    by_cases first_pair : a ≤ i.val ∧ j.val ≤ b
    · constructor
      · intro equal
        have same := first_distinct i j first_pair.1
          (Nat.le_trans (Nat.le_of_lt index_order) first_pair.2)
          (Nat.le_trans first_pair.1 (Nat.le_of_lt index_order)) first_pair.2 equal
        exact (Nat.ne_of_lt index_order) (congrArg Fin.val same)
      · exact first_induced i j first_pair.1 first_pair.2 index_order
    · by_cases second_pair : c ≤ i.val ∧ j.val ≤ d
      · constructor
        · intro equal
          have same := second_distinct i j second_pair.1
            (Nat.le_trans (Nat.le_of_lt index_order) second_pair.2)
            (Nat.le_trans second_pair.1 (Nat.le_of_lt index_order)) second_pair.2 equal
          exact (Nat.ne_of_lt index_order) (congrArg Fin.val same)
        · exact second_induced i j second_pair.1 second_pair.2 index_order
      · by_cases hi_first : a < i.val ∧ i.val < b
        · by_cases hj_second : c < j.val ∧ j.val < d
          · have separated := mutual i j hi_first hj_second
            constructor
            · exact separated.1
            · constructor
              · intro edge
                exact False.elim (separated.2 edge)
              · intro consecutive
                exact False.elim ((ReplacementIndices225.separate_interiors
                  blocks_order hi_first.2 hj_second.1) consecutive)
          · have position := ReplacementIndices225.after_closed hi_first first_pair
            have hj_first : ¬(a < j.val ∧ j.val < b) := position.2.1
            have separated := first_separated i j hi_first hj_second
              (Or.inr position.1)
            rw [agreement j hj_first hj_second]
            constructor
            · exact separated.1
            · constructor
              · intro edge
                exact False.elim (separated.2.1 edge)
              · intro consecutive
                exact False.elim (position.2.2 consecutive)
        · by_cases hi_second : c < i.val ∧ i.val < d
          · have position := ReplacementIndices225.after_closed hi_second second_pair
            have hj_first : ¬(a < j.val ∧ j.val < b) :=
              ReplacementIndices225.after_later blocks_order hi_second.1 index_order
            have hj_second : ¬(c < j.val ∧ j.val < d) := position.2.1
            have separated := second_separated i j hi_second hj_first
              (Or.inr position.1)
            rw [agreement j hj_first hj_second]
            constructor
            · exact separated.1
            · constructor
              · intro edge
                exact False.elim (separated.2.1 edge)
              · intro consecutive
                exact False.elim (position.2.2 consecutive)
          · by_cases hj_first : a < j.val ∧ j.val < b
            · have position := ReplacementIndices225.before_closed hj_first first_pair
              have separated := first_separated j i hj_first hi_second
                (Or.inl position.1)
              rw [agreement i hi_first hi_second]
              constructor
              · intro equal
                exact separated.1 equal.symm
              · constructor
                · intro edge
                  exact False.elim (separated.2.2 edge)
                · intro consecutive
                  exact False.elim (position.2 consecutive)
            · by_cases hj_second : c < j.val ∧ j.val < d
              · have position := ReplacementIndices225.before_closed hj_second second_pair
                have separated := second_separated j i hj_second hi_first
                  (Or.inl position.1)
                rw [agreement i hi_first hi_second]
                constructor
                · intro equal
                  exact separated.1 equal.symm
                · constructor
                  · intro edge
                    exact False.elim (separated.2.2 edge)
                  · intro consecutive
                    exact False.elim (position.2 consecutive)
              · rw [agreement i hi_first hi_second, agreement j hj_first hj_second]
                constructor
                · intro equal
                  have same := p.distinct i j equal
                  exact (Nat.ne_of_lt index_order) (congrArg Fin.val same)
                · exact p.induced i j index_order
  refine { vertex := q, distinct := ?_, induced := ?_ }
  · intro i j equal
    apply Fin.ext
    by_cases forward : i.val < j.val
    · exact False.elim ((pair i j forward).1 equal)
    · by_cases backward : j.val < i.val
      · exact False.elim ((pair j i backward).1 equal.symm)
      · exact ReplacementIndices225.equal_of_nonordered forward backward
  · intro i j index_order
    exact (pair i j index_order).2

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

#print axioms replaceTwoBlocks
#print axioms agreement_of_enlarged_intervals
end Simultaneous225
