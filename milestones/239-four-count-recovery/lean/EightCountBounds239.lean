import EightCountList239

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace EightCountDominance239

theorem seven_term_bounds (M : Int) (hM : 0 ≤ M) (xs : List Int)
    (hlen : xs.length ≤ 7)
    (hxs : ∀ x ∈ xs, -(16 * M) ≤ x ∧ x ≤ 16 * M) :
    -(112 * M) ≤ xs.sum ∧ xs.sum ≤ 112 * M := by
  have h := list_sum_bounds (16 * M) xs hxs
  have hcast : (xs.length : Int) ≤ 7 := Int.ofNat_le.mpr hlen
  have hnonneg : 0 ≤ 16 * M := Int.mul_nonneg (by decide) hM
  have hcap : (xs.length : Int) * (16 * M) ≤ 112 * M := by
    calc
      (xs.length : Int) * (16 * M) ≤ (7 : Int) * (16 * M) :=
        Int.mul_le_mul_of_nonneg_right hcast hnonneg
      _ = 112 * M := by rw [← Int.mul_assoc]; rfl
  exact ⟨Int.le_trans (Int.neg_le_neg hcap) h.1, Int.le_trans h.2 hcap⟩

#print axioms seven_term_bounds

end EightCountDominance239
