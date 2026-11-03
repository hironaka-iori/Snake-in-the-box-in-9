import CanonicalShareAdapter

namespace Snake9.ShareTransfer148
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeAdapter73

theorem share16_of_local_refutation
    (href : RefutedShare [0,1,3,7,15,14,12]
      [(0,21),(0,21),(0,21),(0,21),(0,21)] 12 15)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,3,0,1] ∨
      canon (dsOf p r 6).reverse = [0,1,2,3,0,1]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  change RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15 at href
  exact share_bound_of_either_canonical_match
    p r [0,1,2,3,0,1] hr hshape href

#print axioms share16_of_local_refutation
end Snake9.ShareTransfer148
