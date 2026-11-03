import EndpointGeometry122
import LocalEndpoint26122

namespace Snake9.ActualEndpoint26122
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.EndpointGeometry122

theorem actual_pair26_endpoints {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m) (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (h2 : coreAlpha p (r+2) ≤ 2) (h4 : coreAlpha p (r+4) ≤ 6) :
    ∀ k, k=0 ∨ k=m →
      hamming (vx p (r+2)) (vx p k) = 2 ∧
      hamming (vx p (r+4)) (vx p k) = 2 :=
  actual_endpoints p r 2 6 LocalEndpoint26122.endpoints_in_common hr hshape h2 h4

end Snake9.ActualEndpoint26122
#print axioms Snake9.ActualEndpoint26122.actual_pair26_endpoints
