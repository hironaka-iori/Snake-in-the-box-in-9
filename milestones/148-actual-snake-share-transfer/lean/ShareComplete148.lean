import ShareFromCore148
import ReplayUnsat147

namespace Snake9.ShareTransfer148
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

theorem share16 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,3,0,1] ∨
      canon (dsOf p r 6).reverse = [0,1,2,3,0,1]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum :=
  share16_of_core_unsat Snake9.ReplayFull147.unsat p r hr hshape

#print axioms share16
end Snake9.ShareTransfer148
