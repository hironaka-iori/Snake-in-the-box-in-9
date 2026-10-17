import AggregateWindowUnconditional
import LocalWindowRefuted

/-!
# Unconditional bounds 242 and 241

The premises of `upper_242_of_certified_windows` and `upper_241_of_certified_windows`
are discharged by the kernel-checked local window certificates (`allRefuted`).
-/

namespace Snake9

theorem upper_bound_242 {m : Nat} (p : Snake m) : m ≤ 242 :=
  upper_242_of_refuted LocalWindow.allRefuted p

theorem upper_bound_241 {m : Nat} (p : Snake m) : m ≤ 241 :=
  upper_241_of_refuted LocalWindow.allRefuted p

theorem verified_interval_191_241 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 241 := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_241 p

end Snake9

#print axioms Snake9.upper_bound_242
#print axioms Snake9.upper_bound_241
#print axioms Snake9.verified_interval_191_241
