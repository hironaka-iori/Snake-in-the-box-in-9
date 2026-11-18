import Std

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace EightCountDominance239

theorem list_sum_bounds (B : Int) (xs : List Int)
    (hxs : ∀ x ∈ xs, -B ≤ x ∧ x ≤ B) :
    -((xs.length : Int) * B) ≤ xs.sum ∧
      xs.sum ≤ (xs.length : Int) * B := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hxs a List.mem_cons_self
    have ht := ih (fun x hx => hxs x (List.mem_cons_of_mem a hx))
    simp only [List.sum_cons, List.length_cons, Int.natCast_succ,
      Int.add_mul, Int.one_mul]
    omega

theorem seven_term_bounds (M : Int) (hM : 0 ≤ M) (xs : List Int)
    (hlen : xs.length ≤ 7)
    (hxs : ∀ x ∈ xs, -(16 * M) ≤ x ∧ x ≤ 16 * M) :
    -(112 * M) ≤ xs.sum ∧ xs.sum ≤ 112 * M := by
  have h := list_sum_bounds (16 * M) xs hxs
  have hcast : (xs.length : Int) ≤ 7 := by omega
  have hnonneg : 0 ≤ 16 * M := by omega
  have hmul := Int.mul_le_mul_of_nonneg_right hcast hnonneg
  omega

/-- Generic integer step for an antipodal row with at most seven other terms.
The geometric origin and evenness of the terms are separate hypotheses. -/
theorem even_row_zero (M w s : Int) (xs : List Int)
    (hM : 0 ≤ M) (hmax : w = M ∨ w = -M)
    (hlen : xs.length ≤ 7)
    (hxs : ∀ x ∈ xs, -(16 * M) ≤ x ∧ x ≤ 16 * M)
    (heven : (2 : Int) ∣ xs.sum)
    (hs : -1 ≤ s ∧ s ≤ 1)
    (hrow : 128 * w + xs.sum = 315 * s) : M = 0 := by
  have hs0 : s = 0 := by
    obtain ⟨q, hq⟩ := heven
    omega
  have hbound := seven_term_bounds M hM xs hlen hxs
  rcases hmax with hw | hw <;> omega

#print axioms list_sum_bounds
#print axioms seven_term_bounds
#print axioms even_row_zero

end EightCountDominance239
