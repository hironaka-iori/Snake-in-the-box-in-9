import WindowNormalization
import WindowReversal
import W223RepeatedGeometry
import W223DistinctGeometry
import W223Repeated
import W223Distinct

namespace Snake9
open SquareIncidence Window244
set_option maxHeartbeats 800000

theorem no_two_two_three_internal {m : Nat} (p : Snake m) (r : Nat) (hr : r+4 ≤ m) :
    ¬ (localAlpha p ⟨r+1,by omega⟩ = 2 ∧
       localAlpha p ⟨r+2,by omega⟩ = 2 ∧
       localAlpha p ⟨r+3,by omega⟩ = 3) := by
  rintro ⟨ha,hb,hc⟩
  obtain ⟨q,hα,hv1,hv2,hv3,hshape⟩ := normalize_five_to_standard p r hr
  have hqa := (hα ⟨r+1,by omega⟩).trans ha
  have hqb := (hα ⟨r+2,by omega⟩).trans hb
  have hqc := (hα ⟨r+3,by omega⟩).trans hc
  rcases hshape with hw | hw
  · have ctx := W223RepeatedGeometry.context_of_alpha q (by omega) hw
      ⟨r+1,by omega⟩ hv1 hqa ⟨r+2,by omega⟩ hv2 hqb ⟨r+3,by omega⟩ hv3 hqc
    exact W223Repeated.constraints_unsat _ (W223RepeatedGeometry.constraints q ctx)
  · have ctx := W223DistinctGeometry.context_of_alpha q (by omega) hw
      ⟨r+1,by omega⟩ hv1 hqa ⟨r+2,by omega⟩ hv2 hqb ⟨r+3,by omega⟩ hv3 hqc
    exact W223Distinct.constraints_unsat _ (W223DistinctGeometry.constraints q ctx)

theorem no_three_two_two_internal {m : Nat} (p : Snake m) (r : Nat) (hr : r+4 ≤ m) :
    ¬ (localAlpha p ⟨r+1,by omega⟩ = 3 ∧
       localAlpha p ⟨r+2,by omega⟩ = 2 ∧
       localAlpha p ⟨r+3,by omega⟩ = 2) :=
  no322_of_no223 (fun q r hr => no_two_two_three_internal q r hr) p r hr

#print axioms no_two_two_three_internal
#print axioms no_three_two_two_internal
end Snake9
