import PotentialBlocks102

set_option autoImplicit false

namespace Snake9.BooleanComparison102

theorem ble_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b with
  | false =>
      have hn : ¬ a ≤ b := by
        intro hab
        have ht := Nat.ble_eq_true_of_le hab
        simp [h] at ht
      simp [hn]
  | true =>
      have hl := Nat.le_of_ble_eq_true h
      simp [hl]

#print axioms ble_decide
end Snake9.BooleanComparison102
