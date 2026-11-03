import ActualOuter120
import ReferenceCoverage109

namespace Snake9.ReferenceCoverage120
open Snake9.LocalWindow Snake9.Reference85 Snake9.RecoveredReference108
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem fifteen_reference_entries_refuted :
    AllRefutedList [([0,1,2,0,3,1],[2,3,6,3,2]),
      ([0,1,2,0,3,1],[2,3,6,3,3]),
      ([0,1,2,0,3,1],[3,3,6,3,2]),
      ([0, 1, 2], [1, 1]),
      ([0, 1, 2, 3, 0, 4], [2, 2, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 3, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 4, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 5, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 4, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 6, 2, 2]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 6, 2, 3]),
      ([0, 1, 2, 3, 4], [1, 5, 4, 2]),
      ([0, 1, 2, 3, 4], [1, 5, 5, 1]),
      ([0, 1, 2, 3, 4], [1, 5, 5, 2]),
      ([0, 1, 2, 3, 4], [1, 5, 6, 2])] := by
  refine ⟨refuted_of_tighter_centres Snake9.ActualOuter120.outer_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres Snake9.ActualOuter120.outer_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres Snake9.ActualOuter120.outer_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  exact Snake9.RelaxedGraph109.twelve_reference_entries_refuted

theorem reference_union_iff_remaining_fifteen :
    AllRefutedList referenceKeys ↔
      AllRefutedList (referenceKeys.filter fun k => decide (k ∉ [([0,1,2,0,3,1],[2,3,6,3,2]),
      ([0,1,2,0,3,1],[2,3,6,3,3]),
      ([0,1,2,0,3,1],[3,3,6,3,2]),
      ([0, 1, 2], [1, 1]),
      ([0, 1, 2, 3, 0, 4], [2, 2, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 3, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 4, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 5, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 4, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 6, 2, 2]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 6, 2, 3]),
      ([0, 1, 2, 3, 4], [1, 5, 4, 2]),
      ([0, 1, 2, 3, 4], [1, 5, 5, 1]),
      ([0, 1, 2, 3, 4], [1, 5, 5, 2]),
      ([0, 1, 2, 3, 4], [1, 5, 6, 2])])) :=
  allRefutedList_filter_iff _ _ fifteen_reference_entries_refuted

theorem remaining_fifteen_key_count :
    (referenceKeys.filter fun k => decide (k ∉ [([0,1,2,0,3,1],[2,3,6,3,2]),
      ([0,1,2,0,3,1],[2,3,6,3,3]),
      ([0,1,2,0,3,1],[3,3,6,3,2]),
      ([0, 1, 2], [1, 1]),
      ([0, 1, 2, 3, 0, 4], [2, 2, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 3, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 4, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 5, 6, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 4, 2, 3]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 6, 2, 2]),
      ([0, 1, 2, 3, 0, 4], [2, 6, 6, 2, 3]),
      ([0, 1, 2, 3, 4], [1, 5, 4, 2]),
      ([0, 1, 2, 3, 4], [1, 5, 5, 1]),
      ([0, 1, 2, 3, 4], [1, 5, 5, 2]),
      ([0, 1, 2, 3, 4], [1, 5, 6, 2])])).length = 1363 := by
  decide +kernel

theorem new_reference_indices :
    referenceKeys.getD 126 ([],[]) = ([0,1,2,0,3,1],[2,3,6,3,2]) ∧
    referenceKeys.getD 127 ([],[]) = ([0,1,2,0,3,1],[2,3,6,3,3]) ∧
    referenceKeys.getD 138 ([],[]) = ([0,1,2,0,3,1],[3,3,6,3,2]) := by
  decide +kernel

#print axioms fifteen_reference_entries_refuted
#print axioms reference_union_iff_remaining_fifteen
#print axioms remaining_fifteen_key_count
#print axioms new_reference_indices
end Snake9.ReferenceCoverage120
