import PotentialChecker99
import CompletedPotential99
import ConditionalPotential99

set_option autoImplicit false

namespace Snake9.Potential99
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeAdapter73 Snake9.CountFree98 Snake9.Weights98
open Snake9.PotentialChecker99

theorem completed_upper235
    (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    (hcheck : graphCheck (weight completedCredit) 483 Completed.potential = true)
    {m : Nat} (p : Snake m) : m ≤ 235 :=
  Snake9.PotentialAssembly98.completed_upper235 h235 h236 Completed.potential
    (fun s _ => Completed.potential_le s)
    (graphCheck_sound _ _ _ hcheck) p

theorem conditional_upper234
    (h7301 : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15)
    (h7302 : RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 17)
    (h7303 : RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15)
    (h7307 : RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15)
    (h7308 : RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15)
    (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    (hcheck : graphCheck (weight conditionalCredit) 496 Conditional.potential = true)
    {m : Nat} (p : Snake m) : m ≤ 234 :=
  Snake9.PotentialAssembly98.conditional_upper234 h7301 h7302 h7303 h7307 h7308
    h235 h236 Conditional.potential (fun s _ => Conditional.potential_le s)
    (graphCheck_sound _ _ _ hcheck) p

#print axioms completed_upper235
#print axioms conditional_upper234
#check @completed_upper235
#check @conditional_upper234
end Snake9.Potential99
