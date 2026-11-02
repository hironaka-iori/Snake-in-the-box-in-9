import NewRelaxed109
import ReferenceCoverage108

namespace Snake9.RelaxedGraph109
open Snake9.LocalWindow Snake9.Reference85 Snake9.RecoveredReference108
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem twelve_reference_entries_refuted : AllRefutedList [([0, 1, 2], [1, 1]),
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
  refine ⟨Snake9.RecoveredReference107.adjacent_ones_refuted, ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_reference_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_reference_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_reference_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_reference_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_reference_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_reference_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_reference_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_01234_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_01234_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_01234_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  refine ⟨refuted_of_tighter_centres relaxed_01234_refuted (by
    simp only [Tags.centresK_eq]
    decide +kernel), ?_⟩
  trivial

theorem reference_union_iff_remaining_twelve :
    AllRefutedList referenceKeys ↔
      AllRefutedList (referenceKeys.filter fun k => decide (k ∉ [([0, 1, 2], [1, 1]),
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
  allRefutedList_filter_iff _ _ twelve_reference_entries_refuted

theorem remaining_twelve_key_count :
    (referenceKeys.filter fun k => decide (k ∉ [([0, 1, 2], [1, 1]),
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
      ([0, 1, 2, 3, 4], [1, 5, 6, 2])])).length = 1366 := by
  decide +kernel

#print axioms twelve_reference_entries_refuted
#print axioms reference_union_iff_remaining_twelve
#print axioms remaining_twelve_key_count
end Snake9.RelaxedGraph109
