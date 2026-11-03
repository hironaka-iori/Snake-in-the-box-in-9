import GlobalCharge98
import UniformSixBound124
import SixDeficit124

namespace Snake9.ActualUniform124
open Finset
open scoped BigOperators
open Snake9.LocalWindow Snake9.CountGeometry78 Snake9.SquareIncidence

set_option maxHeartbeats 2000000

-- These are unconditional count facts for an actual nontrivial snake.
-- The square budget follows directly from the incidence identity and wedge bound.
theorem count_bounds {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    4 ≤ coreAlpha p 0 ∧
    4 ≤ coreAlpha p m ∧
    (∀ i, 0 < i → i < m → 1 ≤ coreAlpha p i) ∧
    (∑ i ∈ range (m+1), coreAlpha p i)+35*(m+1) ≤ 9214 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← localAlpha_eq_coreAlpha p 0 (by omega)]
    exact Snake9.endpoint_alpha_ge_four p ⟨0, by omega⟩ hm (Or.inl rfl)
  · rw [← localAlpha_eq_coreAlpha p m (by omega)]
    exact Snake9.endpoint_alpha_ge_four p ⟨m, by omega⟩ hm (Or.inr rfl)
  · intro i _ hi
    exact core_count_positive p i (by omega)
  · rw [Snake9.GlobalCharge98.core_count_total p]
    have hidentity := Snake9.SquareIncidence.global_identity p
    rw [Snake9.SquareIncidence.selected_total p] at hidentity
    have hwedge := Snake9.SquareIncidence.wedge_total_upper p
    omega

-- The universal six-count floor is an explicit remaining hypothesis.
theorem bound233_of_floor26 {m : Nat} (p : Snake m)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      26 ≤ ∑ j ∈ range 6, coreAlpha p (r+j)) :
    m ≤ 233 := by
  by_cases hsmall : m ≤ 233
  · exact hsmall
  have hm : 1 ≤ m := by omega
  obtain ⟨h0, hend, hpos, hsquare⟩ := count_bounds p hm
  exact Snake9.UniformSix124.bound233_of_floor26 (coreAlpha p) m
    h0 hend hpos hfloor hsquare

theorem bound234_of_floor25 {m : Nat} (p : Snake m)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      25 ≤ ∑ j ∈ range 6, coreAlpha p (r+j)) :
    m ≤ 234 := by
  by_cases hsmall : m ≤ 234
  · exact hsmall
  have hm : 1 ≤ m := by omega
  obtain ⟨h0, hend, hpos, hsquare⟩ := count_bounds p hm
  exact Snake9.UniformSix124.bound234_of_floor25 (coreAlpha p) m
    h0 hend hpos hfloor hsquare

-- Natural subtraction measures each block's shortfall below 25.
-- The bound on the sum of shortfalls remains explicit; it is not inferred
-- from the pattern-specific native searches or the endpoint results.
theorem bound234_of_deficit28 {m : Nat} (p : Snake m)
    (hdef : 235 ≤ m →
      (∑ b ∈ range 39,
        (25-∑ j ∈ range 6, coreAlpha p (6*b+j+1))) ≤ 28) :
    m ≤ 234 := by
  by_cases hsmall : m ≤ 234
  · exact hsmall
  have hm : 1 ≤ m := by omega
  obtain ⟨h0, hend, hpos, hsquare⟩ := count_bounds p hm
  exact Snake9.SixDeficit124.bound234_of_deficit28 (coreAlpha p) m
    h0 hend hpos hdef hsquare

#print axioms count_bounds
#print axioms bound233_of_floor26
#print axioms bound234_of_floor25
#print axioms bound234_of_deficit28
end Snake9.ActualUniform124
