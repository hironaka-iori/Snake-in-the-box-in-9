import AggregateDirectionUnconditional
import LocalWindowDirUnsat

/-!
# Unconditional bound 239

The premise of `upper_239_of_refuted` is discharged by the 145 kernel-checked
direction-window refutations (`allRefuted239`).
-/

namespace Snake9

theorem upper_bound_239 {m : Nat} (p : Snake m) : m ≤ 239 :=
  upper_239_of_refuted LocalWindow.allRefuted239 p

theorem verified_interval_191_239 :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ 239 := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_239 p

end Snake9

#print axioms Snake9.upper_bound_239
#print axioms Snake9.verified_interval_191_239
