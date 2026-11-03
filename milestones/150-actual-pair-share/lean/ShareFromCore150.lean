import CanonicalShareAdapter
import Share150.Semantics150

namespace Snake9.ShareTransfer150
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeAdapter73

theorem share16_of_core_unsat
    (hunsat : Unsat ShareWindow150.cnf)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2] ∨
      canon (dsOf p r 6).reverse = [0,1,2,0,3,2]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have href : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15 := by
    simpa only [ShareWindow150.window, ShareWindow150.bounds,
      ShareWindow150.resolution, ShareWindow150.cap, winOf, broadBounds] using
      ShareWindow150.local_share16_of_core_unsat150 hunsat
  exact share_bound_of_either_canonical_match p r [0,1,2,0,3,2] hr hshape href

#print axioms share16_of_core_unsat
end Snake9.ShareTransfer150
