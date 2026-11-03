import CoreSemantics129
import ActualSplit129
import Recovered129G.LocalWindowUnsat.Triple129

namespace Snake9.ActualFourthThree130
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

theorem triple_lower {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hfourth : coreAlpha p (r+4) = 3) :
    12 ≤ coreAlpha p (r+3)+coreAlpha p (r+5)+coreAlpha p (r+6) :=
  CoreSemantics129.actual_triple_lower Triple129.unsat p r hr hshape hfourth

theorem six_lower {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (hfourth : coreAlpha p (r+4) = 3) :
    23 ≤ ∑ j ∈ Finset.range 6, coreAlpha p (r+j+1) :=
  CoreSemantics129.actual_six_lower Triple129.unsat p r hr hshape hfourth

theorem fourth_at_least_four_of_total22 {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,0,3,2,4])
    (htotal : (∑ j ∈ Finset.range 6, coreAlpha p (r+j+1)) ≤ 22) :
    4 ≤ coreAlpha p (r+4) := by
  rcases ActualSplit129.actual_fourth_split p r hr hshape htotal with heq | hlarge
  · have h := six_lower p r hr hshape heq
    omega
  · exact hlarge

end Snake9.ActualFourthThree130

#print axioms Snake9.ActualFourthThree130.triple_lower
#print axioms Snake9.ActualFourthThree130.six_lower
#print axioms Snake9.ActualFourthThree130.fourth_at_least_four_of_total22
