import EightCountBounds239

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace EightCountDominance239

theorem ternary_even_row (w total s : Int)
    (heven : (2 : Int) ∣ total)
    (hs : -1 ≤ s ∧ s ≤ 1)
    (hrow : 128 * w + total = 315 * s) : s = 0 := by
  obtain ⟨q, hq⟩ := heven
  omega

#print axioms ternary_even_row

theorem bounded_extreme_zero (M w total : Int)
    (hM : 0 ≤ M) (hmax : w = M ∨ w = -M)
    (hbound : -(112 * M) ≤ total ∧ total ≤ 112 * M)
    (hrow : 128 * w + total = 0) : M = 0 := by
  rcases hmax with rfl | rfl <;> omega

#print axioms bounded_extreme_zero

/-- Generic integer step for an antipodal row with at most seven other terms.
The geometric origin and evenness of the terms are separate hypotheses. -/
theorem even_row_zero (M w s : Int) (xs : List Int)
    (hM : 0 ≤ M) (hmax : w = M ∨ w = -M)
    (hlen : xs.length ≤ 7)
    (hxs : ∀ x ∈ xs, -(16 * M) ≤ x ∧ x ≤ 16 * M)
    (heven : (2 : Int) ∣ xs.sum)
    (hs : -1 ≤ s ∧ s ≤ 1)
    (hrow : 128 * w + xs.sum = 315 * s) : M = 0 := by
  have hs0 := ternary_even_row w xs.sum s heven hs hrow
  have hbound := seven_term_bounds M hM xs hlen hxs
  have hzero : 128 * w + xs.sum = 0 := by
    simpa only [hs0, Int.mul_zero] using hrow
  exact bounded_extreme_zero M w xs.sum hM hmax hbound hzero

#print axioms even_row_zero

end EightCountDominance239
