import ShareTransfer148
import Share146.Semantics147

namespace Snake9.ShareTransfer148
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

theorem share16_of_core_unsat
    (hunsat : Unsat ShareWindow146.cnf)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,3,0,1] ∨
      canon (dsOf p r 6).reverse = [0,1,2,3,0,1]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  apply share16_of_local_refutation (p := p) (r := r) (hr := hr) (hshape := hshape)
  simpa only [ShareWindow146.window, ShareWindow146.bounds,
    ShareWindow146.resolution, ShareWindow146.cap] using
    ShareWindow146.local_share16_of_core_unsat147 hunsat

#print axioms share16_of_core_unsat
end Snake9.ShareTransfer148
