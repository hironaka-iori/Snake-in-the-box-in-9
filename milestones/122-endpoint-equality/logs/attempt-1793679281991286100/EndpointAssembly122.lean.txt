import EndpointGeometry122
import ActualPair121
import EndpointFrequency122

namespace Snake9.EndpointAssembly122
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.EndpointGeometry122
set_option maxHeartbeats 0

theorem reverse_endpoints {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (h : ∀ k, k=0 ∨ k=m →
      hamming (vx (revSnake p) (m-r-6+2)) (vx (revSnake p) k) = 2 ∧
      hamming (vx (revSnake p) (m-r-6+4)) (vx (revSnake p) k) = 2) :
    ∀ k, k=0 ∨ k=m →
      hamming (vx p (r+2)) (vx p k) = 2 ∧
      hamming (vx p (r+4)) (vx p k) = 2 := by
  have hv2 : vx (revSnake p) (m-r-6+2) = vx p (r+4) := by
    rw [vx_rev p (by omega)]
    congr 1
    omega
  have hv4 : vx (revSnake p) (m-r-6+4) = vx p (r+2) := by
    rw [vx_rev p (by omega)]
    congr 1
    omega
  have hv0 : vx (revSnake p) 0 = vx p m := by simp only [vx_rev p (Nat.zero_le m), Nat.sub_zero]
  have hvm : vx (revSnake p) m = vx p 0 := by simp only [vx_rev p (le_refl m), Nat.sub_self]
  intro k hk
  rcases hk with rfl | rfl
  · simpa only [hv2,hv4,hvm] using (h m (Or.inr rfl)).symm
  · simpa only [hv2,hv4,hv0] using (h 0 (Or.inl rfl)).symm

theorem actual_equality_endpoints
    (h26 : ∀ S E : Nat → Bool,
      Axioms S E (winOf [0,1,2,0,3,2])
        (centresOf (winOf [0,1,2,0,3,2]) [(0,21),(0,2),(0,21),(0,6),(0,21)]) →
      ∀ v, E v = true → v ∈ [0,5,10,15,18,23,34,39,66,71,130,135,258,263])
    (h35 : ∀ S E : Nat → Bool,
      Axioms S E (winOf [0,1,2,0,3,2])
        (centresOf (winOf [0,1,2,0,3,2]) [(0,21),(0,3),(0,21),(0,5),(0,21)]) →
      ∀ v, E v = true → v ∈ [0,5,10,15,18,23,34,39,66,71,130,135,258,263])
    (h44 : ∀ S E : Nat → Bool,
      Axioms S E (winOf [0,1,2,0,3,2])
        (centresOf (winOf [0,1,2,0,3,2]) [(0,21),(0,4),(0,21),(0,4),(0,21)]) →
      ∀ v, E v = true → v ∈ [0,5,10,15,18,23,34,39,66,71,130,135,258,263])
    {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (heq : coreAlpha p (r+2) + coreAlpha p (r+4) = 8) :
    ∀ k, k=0 ∨ k=m →
      hamming (vx p (r+2)) (vx p k) = 2 ∧
      hamming (vx p (r+4)) (vx p k) = 2 := by
  have hmin := ActualPair121.actual_pair_minima p r hr hshape
  by_cases h2 : coreAlpha p (r+2) ≤ 2
  · exact actual_endpoints p r 2 6 h26 hr hshape h2 (by omega)
  by_cases h3 : coreAlpha p (r+2) ≤ 3
  · exact actual_endpoints p r 3 5 h35 hr hshape h3 (by omega)
  by_cases h4 : coreAlpha p (r+2) ≤ 4
  · exact actual_endpoints p r 4 4 h44 hr hshape h4 (by omega)
  have hs : canon (dsOf (revSnake p) (m-r-6) 6) = [0,1,2,0,3,2] := by
    rw [dsOf_rev p r 6 hr, ← reverse_canon, hshape]
    rfl
  have ha2 : coreAlpha (revSnake p) (m-r-6+2) = coreAlpha p (r+4) := by
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega
  have ha4 : coreAlpha (revSnake p) (m-r-6+4) = coreAlpha p (r+2) := by
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega
  apply reverse_endpoints p r hr
  by_cases hrev2 : coreAlpha p (r+4) ≤ 2
  · apply actual_endpoints (revSnake p) (m-r-6) 2 6 h26 (by omega) hs
    · rw [ha2]; exact hrev2
    · rw [ha4]; omega
  · apply actual_endpoints (revSnake p) (m-r-6) 3 5 h35 (by omega) hs
    · rw [ha2]; omega
    · rw [ha4]; omega

end Snake9.EndpointAssembly122
#print axioms Snake9.EndpointAssembly122.reverse_endpoints
#print axioms Snake9.EndpointAssembly122.actual_equality_endpoints
