import AggregateDirection238Unconditional
import LocalWindowDirUnsat5

/-!
# Unconditional bound 238

The premise of `upper_238_of_refuted` is discharged by the 325 kernel-checked
five-centre window refutations (`allRefuted238`).
-/

namespace Snake9

theorem upper_bound_238 {m : Nat} (p : Snake m) : m ≤ 238 :=
  upper_238_of_refuted LocalWindow.allRefuted238 p

theorem verified_interval_191_238 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 238 := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_238 p

end Snake9

#print axioms Snake9.upper_bound_238
#print axioms Snake9.verified_interval_191_238
