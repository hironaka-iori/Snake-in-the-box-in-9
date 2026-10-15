import Std

namespace BooleanCounterLogic

/-- Four clauses describe a threshold-counter transition exactly. -/
theorem transition_iff (a b c s : Bool) :
    ((a = false ∨ s = true) ∧
     (b = false ∨ c = false ∨ s = true) ∧
     (s = false ∨ a = true ∨ b = true) ∧
     (s = false ∨ a = true ∨ c = true)) ↔
    s = (a || (b && c)) := by
  cases a <;> cases b <;> cases c <;> cases s <;> decide

/-- Adding one Boolean event updates every positive count threshold. -/
theorem threshold_increment (n j : Nat) (b : Bool) :
    (j + 1 ≤ n + (if b then 1 else 0)) ↔
      (j + 1 ≤ n ∨ (b = true ∧ j ≤ n)) := by
  cases b <;> simp <;> omega

/-- Appending an event gives the same recurrence for list prefix counts. -/
theorem prefix_threshold (xs : List Bool) (b : Bool) (j : Nat) :
    (j + 1 ≤ (xs ++ [b]).count true) ↔
      (j + 1 ≤ xs.count true ∨ (b = true ∧ j ≤ xs.count true)) := by
  cases b <;> simp <;> omega

#print axioms transition_iff
#print axioms threshold_increment
#print axioms prefix_threshold
end BooleanCounterLogic
