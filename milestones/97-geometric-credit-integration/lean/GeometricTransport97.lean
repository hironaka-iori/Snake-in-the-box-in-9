import GeometricData97
import ConcreteRules95
import Port97M59GeometryBatch00

namespace Snake9.GeometricCredit97
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeAdapter73 Snake9.Direction77 Snake9.CreditTransport95
open Snake9.GraphWalk78 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.CountGeometry78

set_option maxHeartbeats 2000000

theorem actual_geometric_credit_from_catalogue
    (hvalid : ∀ i, i < 505 →
      LocalNineShare (extensions.getD i []) (geometricCredits.getD i 0))
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    geometricCredits.getD (directionId p r) 0 ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  obtain ⟨P,hP⟩ := canonical_permutation p r 9 hr
  apply hvalid (directionId p r) (directionId_lt p r hr) p P r hr
  intro j hj
  rw [direction_decode p r hr] at hj ⊢
  have hj9 : j < 9 := by simpa [length_canon, dsOf] using hj
  exact hP j hj9

theorem actual_geometric_history_credit_from_catalogue
    (hvalid : ∀ i, i < 505 →
      LocalNineShare (extensions.getD i []) (geometricCredits.getD i 0))
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    max (geometricCredits.getD (directionId p r) 0)
      (historyCredit concreteRules (actualHistory p r) (directionId p r) (sixCode p r)) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  exact max_le (actual_geometric_credit_from_catalogue hvalid p r hr)
    (concrete_actual_history_credit p r hr)

theorem actual_geometric_history_weight_from_catalogue
    (hvalid : ∀ i, i < 505 →
      LocalNineShare (extensions.getD i []) (geometricCredits.getD i 0))
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    120 * (sixCode p r % 6 + 1) +
      max (geometricCredits.getD (directionId p r) 0)
        (historyCredit concreteRules (actualHistory p r) (directionId p r) (sixCode p r)) ≤
      120 * coreAlpha p (r+8) +
        ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  rw [(sixCode_spec p r hr).2.2.2]
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 120 (Nat.min_le_right 6 (coreAlpha p (r+8))))
    (actual_geometric_history_credit_from_catalogue hvalid p r hr)

#print axioms actual_geometric_credit_from_catalogue
#print axioms actual_geometric_history_credit_from_catalogue
#print axioms actual_geometric_history_weight_from_catalogue
#print axioms Snake9.LocalWindow.ExtendedShare59.G000.in_snake

end Snake9.GeometricCredit97
