import AggregateDirection236Unconditional
import LocalWindowDirUnsatR4

/-!
# Unconditional bound 236

The premise of `upper_236_of_refuted` is discharged by the 732 kernel-checked
five-centre window refutations (`allRefuted236`).
-/

namespace Snake9

theorem upper_bound_236 {m : Nat} (p : Snake m) : m ≤ 236 :=
  upper_236_of_refuted LocalWindow.allRefuted236 p

theorem verified_interval_191_236 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 236 := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_236 p

end Snake9

#print axioms Snake9.upper_bound_236
#print axioms Snake9.verified_interval_191_236
