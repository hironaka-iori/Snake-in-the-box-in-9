import ReferenceInterface

namespace Snake9.GuardedCharge123
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

-- If the first count is recorded exactly, all six-count deficit belongs
-- to the last five positions, so the existing coefficient 24 is retained.
theorem six_sum_last_five_credit (alpha : Nat → Nat) (r L : Nat)
    (hfirst : alpha r ≤ 6)
    (hlocal : L ≤ ∑ j ∈ range 6, alpha (r+j)) :
    24 * (L - ∑ j ∈ range 6, min 6 (alpha (r+j))) ≤
      24 * ∑ j ∈ range 5, (alpha (r+j+1) - min 6 (alpha (r+j+1))) := by
  have h1 := Nat.min_le_right 6 (alpha (r+1))
  have h2 := Nat.min_le_right 6 (alpha (r+2))
  have h3 := Nat.min_le_right 6 (alpha (r+3))
  have h4 := Nat.min_le_right 6 (alpha (r+4))
  have h5 := Nat.min_le_right 6 (alpha (r+5))
  have h0 : min 6 (alpha r) = alpha r := min_eq_right hfirst
  apply Nat.mul_le_mul_left
  norm_num [Finset.sum_range_succ, Nat.add_assoc] at hlocal ⊢
  omega

theorem maximum_preserves_five_credit (a b E : Nat)
    (ha : a ≤ 24*E) (hb : b ≤ 24*E) : max a b ≤ 24*E :=
  max_le ha hb

#print axioms six_sum_last_five_credit
#print axioms maximum_preserves_five_credit
end Snake9.GuardedCharge123
