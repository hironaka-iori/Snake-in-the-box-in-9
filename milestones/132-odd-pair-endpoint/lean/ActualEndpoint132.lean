import CoreSemantics132
import Recovered132G.LocalWindowUnsat.Endpoint132
import EndpointGeometry122

namespace Snake9.ActualEndpoint132
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.EndpointGeometry122

set_option maxHeartbeats 2000000

theorem actual_pair_endpoint {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (hpair : coreAlpha p (r+2)+coreAlpha p (r+4) ≤ 9) :
    ∃ k, (k=0 ∨ k=m) ∧
      hamming (vx p (r+2)) (vx p k) = 2 ∧
      hamming (vx p (r+4)) (vx p k) = 2 := by
  obtain ⟨P,hP⟩ := ActualCounters132.actual_normalized_frame p r hr hshape
  obtain ⟨v,hv,he⟩ := CoreSemantics132.actual_frame_endpoint Endpoint132.unsat p P r hr hP hpair
  have hcommon : v ∈ [0,5,10,15,18,23,34,39,66,71,130,135,258,263] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv ⊢
    tauto
  have hk : ∃ k, (k=0 ∨ k=m) ∧ v = amap P (vx p r) (vx p k) := by
    rcases (frameE_cases p P he).2 with h0 | hm
    · exact ⟨0,Or.inl rfl,h0⟩
    · exact ⟨m,Or.inr rfl,hm⟩
  obtain ⟨k,hk,hvk⟩ := hk
  have hc2 := frame_window p P r (canon_winOf [0,1,2,0,3,2]) hr hP 2 (by decide)
  have hc4 := frame_window p P r (canon_winOf [0,1,2,0,3,2]) hr hP 4 (by decide)
  change 3 = amap P (vx p r) (vx p (r+2)) at hc2
  change 6 = amap P (vx p r) (vx p (r+4)) at hc4
  refine ⟨k,hk,?_,?_⟩
  · obtain ⟨i,j,hi,hj,hij,hz⟩ := common_sphere_two_flips hcommon 3 (Or.inl rfl)
    obtain ⟨i',j',hi',hj',hij',hz'⟩ :=
      pullback_two_flips P (vx p r) (vx p (r+2)) (vx p k) i j
        (vx_lt p r) (vx_lt p (r+2)) (vx_lt p k) hi hj hij
        (by rw [← hc2,← hvk]; exact hz)
    rw [hz']
    exact two_flips_distance _ i' j' hi' hj' hij'
  · obtain ⟨i,j,hi,hj,hij,hz⟩ := common_sphere_two_flips hcommon 6 (Or.inr rfl)
    obtain ⟨i',j',hi',hj',hij',hz'⟩ :=
      pullback_two_flips P (vx p r) (vx p (r+4)) (vx p k) i j
        (vx_lt p r) (vx_lt p (r+4)) (vx_lt p k) hi hj hij
        (by rw [← hc4,← hvk]; exact hz)
    rw [hz']
    exact two_flips_distance _ i' j' hi' hj' hij'

theorem actual_pair_ge_ten_without_endpoint {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (hnone : ∀ k, k=0 ∨ k=m →
      ¬ (hamming (vx p (r+2)) (vx p k) = 2 ∧
        hamming (vx p (r+4)) (vx p k) = 2)) :
    10 ≤ coreAlpha p (r+2)+coreAlpha p (r+4) := by
  by_contra hn
  obtain ⟨k,hk,h2,h4⟩ := actual_pair_endpoint p r hr hshape (by omega)
  exact hnone k hk ⟨h2,h4⟩

#print axioms actual_pair_endpoint
#print axioms actual_pair_ge_ten_without_endpoint
end Snake9.ActualEndpoint132
