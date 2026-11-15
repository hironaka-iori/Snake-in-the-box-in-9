import LayerJoining
import ReplacementCases225
import ReplacementPairs225

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
  have pair : ∀ i j : Fin (n + 1), i.val < j.val →
      q i ≠ q j ∧ (R (q i) (q j) ↔ i.val + 1 = j.val) := by
    intro i j indices
    rcases ReplacementCases225.classify (a := a) (d := d) ordered.2.1 indices with
      h | h | h | h | h | h | h | h
    · exact ReplacementPairs225.local_pair q a b first_distinct first_induced i j indices h
    · exact ReplacementPairs225.local_pair q c d second_distinct second_induced i j indices h
    · have separated := mutual i j h.1 h.2.1
      exact ReplacementPairs225.separated_pair h.2.2 separated.1 separated.2
    · exact ReplacementPairs225.right_pair (agreement j h.2.1 h.2.2.1)
        h.2.2.2.2 (first_separated i j h.1 h.2.2.1 (Or.inr h.2.2.2.1))
    · exact ReplacementPairs225.right_pair (agreement j h.2.1 h.2.2.1)
        h.2.2.2.2 (second_separated i j h.1 h.2.1 (Or.inr h.2.2.2.1))
    · exact ReplacementPairs225.left_pair (agreement i h.1 h.2.1)
        h.2.2.2.2 (first_separated j i h.2.2.1 h.2.1 (Or.inl h.2.2.2.1))
    · exact ReplacementPairs225.left_pair (agreement i h.1 h.2.1)
        h.2.2.2.2 (second_separated j i h.2.2.1 h.1 (Or.inl h.2.2.2.1))
    · exact ReplacementPairs225.retained_pair p q i j indices
        (agreement i h.1 h.2.1) (agreement j h.2.2.1 h.2.2.2)
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
