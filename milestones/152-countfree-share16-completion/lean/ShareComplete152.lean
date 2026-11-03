import ShareFromCore150
import ReplayUnsat150

namespace Snake9.ShareTransfer152
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

theorem share16 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2] ∨
      canon (dsOf p r 6).reverse = [0,1,2,0,3,2]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum :=
  Snake9.ShareTransfer150.share16_of_core_unsat Snake9.ReplayFull150.unsat p r hr hshape

#print axioms share16
end Snake9.ShareTransfer152
