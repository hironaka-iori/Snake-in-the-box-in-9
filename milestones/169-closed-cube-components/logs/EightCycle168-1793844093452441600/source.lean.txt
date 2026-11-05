namespace Snake9.Undominated168

def bitCount (b : Bool) : Nat := if b then 1 else 0

theorem eight_cycle_endpoints : ∀ a b c d : Bool,
    1 ≤ bitCount a + bitCount b →
    1 ≤ bitCount b + bitCount c →
    1 ≤ bitCount c + bitCount d →
    1 ≤ bitCount d + bitCount a →
    ¬ (a = true ∧ b = true ∧ c = true ∧ d = true) →
    2 ≤ (if bitCount a + bitCount b = 1 then 1 else 0) +
        (if bitCount b + bitCount c = 1 then 1 else 0) +
        (if bitCount c + bitCount d = 1 then 1 else 0) +
        (if bitCount d + bitCount a = 1 then 1 else 0) := by decide

#print axioms eight_cycle_endpoints
end Snake9.Undominated168
