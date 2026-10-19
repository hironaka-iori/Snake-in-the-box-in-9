import AggregateDirection237Unconditional
import LocalWindowDirUnsatR4b

/-!
# Unconditional bound 237

The premise of `upper_237_of_refuted` is discharged by the 387 kernel-checked
five-centre window refutations (`allRefuted237`).
-/

namespace Snake9

theorem upper_bound_237 {m : Nat} (p : Snake m) : m ≤ 237 :=
  upper_237_of_refuted LocalWindow.allRefuted237 p

theorem verified_interval_191_237 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 237 := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_237 p

end Snake9

#print axioms Snake9.upper_bound_237
#print axioms Snake9.verified_interval_191_237
