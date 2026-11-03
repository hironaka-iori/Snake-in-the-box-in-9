import Structural125

namespace Snake9.EmptyTradeoff125
open Finset
open scoped BigOperators
open Snake9.LocalWindow Snake9.SquareIncidence
set_option maxHeartbeats 2000000

-- Six ordinary empty squares give 24 anchored incidences.
theorem bound234_of_floor24_and_six_empty {m : Nat} (p : Snake m)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      24 ≤ ∑ j ∈ range 6, coreAlpha p (r+j))
    (hempty : 235 ≤ m → 24 ≤ totalEmptyAnchored p) : m ≤ 234 := by
  by_contra h
  have hm : 235 ≤ m := by omega
  obtain ⟨h0,hend,hpos,_⟩ := Snake9.ActualUniform124.count_bounds p (by omega)
  have hc := Snake9.UniformSix124.total_lower_of_six_floor
    (coreAlpha p) m 39 24 (by omega) h0 hend hpos hfloor
  norm_num at hc
  have hs := Snake9.Structural125.retained_square_budget p (by omega)
  have he := hempty hm
  omega

-- Twenty-five ordinary empty squares give 100 anchored incidences.
theorem bound234_of_floor23_and_twenty_five_empty {m : Nat} (p : Snake m)
    (hfloor : ∀ r, 0 < r → r+5 < m →
      23 ≤ ∑ j ∈ range 6, coreAlpha p (r+j))
    (hempty : 235 ≤ m → 100 ≤ totalEmptyAnchored p) : m ≤ 234 := by
  by_contra h
  have hm : 235 ≤ m := by omega
  obtain ⟨h0,hend,hpos,_⟩ := Snake9.ActualUniform124.count_bounds p (by omega)
  have hc := Snake9.UniformSix124.total_lower_of_six_floor
    (coreAlpha p) m 39 23 (by omega) h0 hend hpos hfloor
  norm_num at hc
  have hs := Snake9.Structural125.retained_square_budget p (by omega)
  have he := hempty hm
  omega

#print axioms bound234_of_floor24_and_six_empty
#print axioms bound234_of_floor23_and_twenty_five_empty
end Snake9.EmptyTradeoff125
