import ActualPair121
import ReferenceCoverage120

namespace Snake9.ReferenceCoverage121
open Snake9.LocalWindow Snake9.Reference85 Snake9.RecoveredReference108
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem twenty_reference_entries_refuted :
    AllRefutedList [([0,1,2,0,3,2],[2,2,6,5,2]),
      ([0,1,2,0,3,2],[2,2,6,5,3]),
      ([0,1,2,0,3,2],[2,3,6,3,2]),
      ([0,1,2,0,3,2],[2,3,6,3,3]),
      ([0,1,2,0,3,2],[2,3,6,3,4]),
      ([0,1,2,0,3,1],[2,3,6,3,2]),
      ([0,1,2,0,3,1],[2,3,6,3,3]),
      ([0,1,2,0,3,1],[3,3,6,3,2]),
      ([0,1,2],[1,1]),
      ([0,1,2,3,0,4],[2,2,6,2,3]),
      ([0,1,2,3,0,4],[2,3,6,2,3]),
      ([0,1,2,3,0,4],[2,4,6,2,3]),
      ([0,1,2,3,0,4],[2,5,6,2,3]),
      ([0,1,2,3,0,4],[2,6,4,2,3]),
      ([0,1,2,3,0,4],[2,6,6,2,2]),
      ([0,1,2,3,0,4],[2,6,6,2,3]),
      ([0,1,2,3,4],[1,5,4,2]),
      ([0,1,2,3,4],[1,5,5,1]),
      ([0,1,2,3,4],[1,5,5,2]),
      ([0,1,2,3,4],[1,5,6,2])] := by
  refine ⟨refuted_of_tighter_centres Snake9.ActualPair121.pair25_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres Snake9.ActualPair121.pair25_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres Snake9.ActualPair121.pair34_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres Snake9.ActualPair121.pair34_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres Snake9.ActualPair121.pair34_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  exact Snake9.ReferenceCoverage120.fifteen_reference_entries_refuted

theorem reference_union_iff_remaining_twenty :
    AllRefutedList referenceKeys ↔
      AllRefutedList (referenceKeys.filter fun k => decide (k ∉ [([0,1,2,0,3,2],[2,2,6,5,2]),
      ([0,1,2,0,3,2],[2,2,6,5,3]),
      ([0,1,2,0,3,2],[2,3,6,3,2]),
      ([0,1,2,0,3,2],[2,3,6,3,3]),
      ([0,1,2,0,3,2],[2,3,6,3,4]),
      ([0,1,2,0,3,1],[2,3,6,3,2]),
      ([0,1,2,0,3,1],[2,3,6,3,3]),
      ([0,1,2,0,3,1],[3,3,6,3,2]),
      ([0,1,2],[1,1]),
      ([0,1,2,3,0,4],[2,2,6,2,3]),
      ([0,1,2,3,0,4],[2,3,6,2,3]),
      ([0,1,2,3,0,4],[2,4,6,2,3]),
      ([0,1,2,3,0,4],[2,5,6,2,3]),
      ([0,1,2,3,0,4],[2,6,4,2,3]),
      ([0,1,2,3,0,4],[2,6,6,2,2]),
      ([0,1,2,3,0,4],[2,6,6,2,3]),
      ([0,1,2,3,4],[1,5,4,2]),
      ([0,1,2,3,4],[1,5,5,1]),
      ([0,1,2,3,4],[1,5,5,2]),
      ([0,1,2,3,4],[1,5,6,2])])) :=
  allRefutedList_filter_iff _ _ twenty_reference_entries_refuted

theorem remaining_twenty_key_count :
    (referenceKeys.filter fun k => decide (k ∉ [([0,1,2,0,3,2],[2,2,6,5,2]),
      ([0,1,2,0,3,2],[2,2,6,5,3]),
      ([0,1,2,0,3,2],[2,3,6,3,2]),
      ([0,1,2,0,3,2],[2,3,6,3,3]),
      ([0,1,2,0,3,2],[2,3,6,3,4]),
      ([0,1,2,0,3,1],[2,3,6,3,2]),
      ([0,1,2,0,3,1],[2,3,6,3,3]),
      ([0,1,2,0,3,1],[3,3,6,3,2]),
      ([0,1,2],[1,1]),
      ([0,1,2,3,0,4],[2,2,6,2,3]),
      ([0,1,2,3,0,4],[2,3,6,2,3]),
      ([0,1,2,3,0,4],[2,4,6,2,3]),
      ([0,1,2,3,0,4],[2,5,6,2,3]),
      ([0,1,2,3,0,4],[2,6,4,2,3]),
      ([0,1,2,3,0,4],[2,6,6,2,2]),
      ([0,1,2,3,0,4],[2,6,6,2,3]),
      ([0,1,2,3,4],[1,5,4,2]),
      ([0,1,2,3,4],[1,5,5,1]),
      ([0,1,2,3,4],[1,5,5,2]),
      ([0,1,2,3,4],[1,5,6,2])])).length = 1358 := by
  decide +kernel

theorem new_reference_indices :
    referenceKeys.getD 196 ([],[]) = ([0,1,2,0,3,2],[2,2,6,5,2]) ∧
    referenceKeys.getD 197 ([],[]) = ([0,1,2,0,3,2],[2,2,6,5,3]) ∧
    referenceKeys.getD 198 ([],[]) = ([0,1,2,0,3,2],[2,3,6,3,2]) ∧
    referenceKeys.getD 199 ([],[]) = ([0,1,2,0,3,2],[2,3,6,3,3]) ∧
    referenceKeys.getD 200 ([],[]) = ([0,1,2,0,3,2],[2,3,6,3,4]) := by
  decide +kernel

#print axioms twenty_reference_entries_refuted
#print axioms reference_union_iff_remaining_twenty
#print axioms remaining_twenty_key_count
#print axioms new_reference_indices
end Snake9.ReferenceCoverage121
