import Window223Exclusion
import Aggregate244Conditional

namespace Snake9

theorem upper_bound_244 {m : Nat} (p : Snake m) : m ≤ 244 :=
  upper_244_of_no_two_two_three p (no_two_two_three_internal p)

theorem verified_interval_191_244 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 244 := by
  refine ⟨lower_bound,?_⟩
  rintro m ⟨p⟩
  exact upper_bound_244 p

#print axioms upper_bound_244
#print axioms verified_interval_191_244
end Snake9
