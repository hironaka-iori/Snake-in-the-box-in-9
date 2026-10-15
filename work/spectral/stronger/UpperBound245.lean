import SharedOuterExclusion
import NormalizeSharedThreeTwos
import Aggregate245Conditional

namespace Snake9
open SquareIncidence

theorem no_three_consecutive_internal_twos {m : Nat} (p : Snake m)
    (r : Nat) (hr : r+4≤m) :
    ¬(localAlpha p ⟨r+1,by omega⟩=2 ∧ localAlpha p ⟨r+2,by omega⟩=2 ∧
      localAlpha p ⟨r+3,by omega⟩=2) := by
  rintro ⟨h1,h2,h3⟩
  obtain ⟨h⟩ := normalize_three_twos_to_shared p r hr h1 h2 h3
  exact h.shared.impossible h.middle h.middle_card

theorem upper_bound_245 {m : Nat} (p : Snake m) : m≤245 :=
  upper_245_of_no_three_twos p (no_three_consecutive_internal_twos p)

theorem verified_interval_191_245 :
    Nonempty (Snake 191) ∧ ∀m,Nonempty (Snake m) → m≤245 := by
  refine ⟨lower_bound,?_⟩
  rintro m ⟨p⟩
  exact upper_bound_245 p

#print axioms no_three_consecutive_internal_twos
#print axioms upper_bound_245
#print axioms verified_interval_191_245
end Snake9
