import CountConditionedCredits98
import CountFreeCredits98
import ActualGraphKeys98

namespace Snake9.Weights98
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.GraphWalk78 Snake9.HistoryCredit95
open Snake9.ConcreteCatalogue95 Snake9.GeometricCredit97 Snake9.CountGeometry78
open Snake9.Conditioned98 Snake9.CountFree98 Snake9.CountFreeAdapter73

/-- All alternatives bound the same five shares, so they combine by maximum. -/
def weight (floor : Nat → Nat) (q di code : Nat) : Nat :=
  120*(code % 6+1) +
    max (max (geometricCredits.getD di 0) (historyCredit concreteRules q di code))
      (max (conditionedCredit di code) (floor di))

theorem actual_weight_bound (floor : Nat → Nat)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m)
    (hfloor : floor (directionId p r) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum) :
    weight floor (actualHistory p r) (directionId p r) (sixCode p r) ≤
      120*coreAlpha p (r+8) +
        ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  unfold weight
  apply Nat.add_le_add
  · rw [(sixCode_spec p r hr).2.2.2]
    exact Nat.mul_le_mul_left 120 (Nat.min_le_right 6 (coreAlpha p (r+8)))
  · exact max_le (actual_geometric_history_credit p r hr)
      (max_le (actual_conditioned_credit p r hr) hfloor)

theorem completed_actual_weight {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    weight completedCredit (actualHistory p r) (directionId p r) (sixCode p r) ≤
      120*coreAlpha p (r+8) +
        ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=
  actual_weight_bound completedCredit p r hr (actual_completed_credit p r hr)

theorem conditional_actual_weight
    (h7301 : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15)
    (h7302 : RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 17)
    (h7303 : RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15)
    (h7307 : RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15)
    (h7308 : RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    weight conditionalCredit (actualHistory p r) (directionId p r) (sixCode p r) ≤
      120*coreAlpha p (r+8) +
        ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=
  actual_weight_bound conditionalCredit p r hr
    (actual_conditional_credit h7301 h7302 h7303 h7307 h7308 p r hr)

#print axioms actual_weight_bound
#print axioms completed_actual_weight
#print axioms conditional_actual_weight
end Snake9.Weights98
