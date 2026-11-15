import Std

set_option Elab.async false

namespace ReplacementIndices225

-- Arithmetic is isolated from the constructor's path and relation hypotheses.
theorem after_closed {a b i j : Nat}
    (inside : a < i ∧ i < b) (outside : ¬(a ≤ i ∧ j ≤ b)) :
    b < j ∧ ¬(a < j ∧ j < b) ∧ i + 1 ≠ j := by omega

theorem before_closed {a b i j : Nat}
    (inside : a < j ∧ j < b) (outside : ¬(a ≤ i ∧ j ≤ b)) :
    i < a ∧ i + 1 ≠ j := by omega

theorem separate_interiors {b c i j : Nat}
    (blocks : b ≤ c) (first : i < b) (second : c < j) :
    i + 1 ≠ j := by omega

theorem after_later {a b c i j : Nat}
    (blocks : b ≤ c) (later : c < i) (indices : i < j) :
    ¬(a < j ∧ j < b) := by omega

theorem equal_of_nonordered {i j : Nat}
    (forward : ¬i < j) (backward : ¬j < i) : i = j := by omega

theorem outside_enlarged {a b a' b' i : Nat}
    (left : a' ≤ a) (right : b ≤ b')
    (outside : ¬(a' < i ∧ i < b')) : ¬(a < i ∧ i < b) := by omega

#print axioms after_closed
#print axioms before_closed
#print axioms separate_interiors
#print axioms after_later
#print axioms equal_of_nonordered
#print axioms outside_enlarged
end ReplacementIndices225
