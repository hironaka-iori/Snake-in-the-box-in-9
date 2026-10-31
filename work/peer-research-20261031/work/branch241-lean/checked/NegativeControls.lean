import ScoreAlgebra

namespace Q9ScoreNegativeControls
-- Removing the SAT premise must not prove q>=23: alpha=1,e2=e3=V=0 gives q=21.
theorem missingSATPremiseFalse : ¬ (∀ alpha e2 e3 bonus : Nat,
    1 ≤ alpha → 3*e3 ≤ 6*e2 → bonus ≤ 4*e2 →
    23 ≤ 21*alpha + 2*e2 + e3 + bonus) := by
  intro h
  have bad := h 1 0 0 0 (by decide) (by decide) (by decide)
  omega
-- Dropping singleton is also invalid: alpha=0,e2=11 gives q=22.
theorem missingSingletonFalse : ¬ (∀ alpha e2 e3 bonus : Nat,
    3*e3 ≤ 6*e2 → bonus ≤ 4*e2 →
    22 ≤ 21*alpha + 2*e2 + e3 + bonus →
    23 ≤ 21*alpha + 2*e2 + e3 + bonus) := by
  intro h
  have bad := h 0 11 0 0 (by decide) (by decide) (by decide)
  omega
#print axioms missingSATPremiseFalse
#print axioms missingSingletonFalse
end Q9ScoreNegativeControls
