import EndpointAssembly122
import EndpointFrequencyTight122
import LocalEndpoint26122
import LocalEndpoint35122
import LocalEndpoint44122

namespace Snake9.ActualEndpoint122
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.EndpointGeometry122

theorem actual_equality_endpoints {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m) (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (heq : coreAlpha p (r+2) + coreAlpha p (r+4) = 8) :
    ∀ k, k=0 ∨ k=m →
      hamming (vx p (r+2)) (vx p k) = 2 ∧
      hamming (vx p (r+4)) (vx p k) = 2 :=
  EndpointAssembly122.actual_equality_endpoints
    LocalEndpoint26122.endpoints_in_common LocalEndpoint35122.endpoints_in_common
    LocalEndpoint44122.endpoints_in_common p r hr hshape heq

theorem equality_count_le_thirteen {m : Nat} (p : Snake m) (I : Finset Nat)
    (hfit : ∀ r ∈ I, r+6 ≤ m)
    (hshape : ∀ r ∈ I, canon (dsOf p r 6) = [0,1,2,0,3,2])
    (heq : ∀ r ∈ I, coreAlpha p (r+2) + coreAlpha p (r+4) = 8) :
    I.card ≤ 13 := by
  apply EndpointFrequencyTight122.pair_window_count_le_thirteen p I hfit
  intro r hr
  have h := actual_equality_endpoints p r (hfit r hr) (hshape r hr) (heq r hr)
  exact ⟨⟨(h 0 (Or.inl rfl)).1,(h m (Or.inr rfl)).1⟩,
    ⟨(h 0 (Or.inl rfl)).2,(h m (Or.inr rfl)).2⟩⟩

end Snake9.ActualEndpoint122
#print axioms Snake9.ActualEndpoint122.actual_equality_endpoints
#print axioms Snake9.ActualEndpoint122.equality_count_le_thirteen
