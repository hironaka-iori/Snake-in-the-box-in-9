import Std

set_option Elab.async false

namespace CrossingAllocation229

/-- An upper-anchor count is a lower bound for a matching-parity crossing
count, provided two upper anchors exclude a zero-crossing path. -/
theorem desired_le_actual (A a : Nat) (hA : A ≤ 2)
    (hparity : a % 2 = A % 2) (hpositive : A = 2 → 0 < a) :
    A ≤ a := by
  have hcases : A = 0 ∨ A = 1 ∨ A = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · omega
  · omega
  · have ha := hpositive rfl
    omega

/-- If the available total equals the two upper-anchor counts, the parity
and zero-crossing restrictions force each count separately. -/
theorem forced_allocation (A B a b : Nat) (hA : A ≤ 2) (hB : B ≤ 2)
    (hparityA : a % 2 = A % 2) (hparityB : b % 2 = B % 2)
    (hpositiveA : A = 2 → 0 < a) (hpositiveB : B = 2 → 0 < b)
    (htotal : a + b = A + B) : a = A ∧ b = B := by
  have ha := desired_le_actual A a hA hparityA hpositiveA
  have hb := desired_le_actual B b hB hparityB hpositiveB
  omega

#print axioms desired_le_actual
#print axioms forced_allocation

end CrossingAllocation229
