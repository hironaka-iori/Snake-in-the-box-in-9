import CoreSemantics132
import Recovered132G.LocalWindowUnsat.Endpoint132

namespace Snake9.CommonNeighbor134
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

set_option maxHeartbeats 2000000

theorem pullback_neighbor (P : CPerm) (t z w : Nat)
    (ht : t < 512) (hz : z < 512) (hw : w < 512)
    (h : amap P t w ∈ nbrs (amap P t z)) : w ∈ nbrs z := by
  obtain ⟨k,hk,he⟩ := (mem_nbrs _ _).mp h
  apply (mem_nbrs _ _).mpr
  refine ⟨P.bwd k,P.bwd_lt k hk,?_⟩
  apply amap_inj P ht hw (xor_pow_lt hz (P.bwd_lt k hk))
  rw [amap_flip P t z (P.bwd_lt k hk),P.fwd_bwd k hk]
  exact he

theorem actual_common_neighbor {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (hpair : coreAlpha p (r+2)+coreAlpha p (r+4) ≤ 9) :
    ∃ e z : Nat, (e=0 ∨ e=m) ∧ z < 512 ∧
      sel p (fun v => v) z = false ∧ vx p e ∈ nbrs z ∧
      ∀ j, j < 4 → vx p (r+2*j) ∈ nbrs z := by
  obtain ⟨P,hP⟩ := ActualCounters132.actual_normalized_frame p r hr hshape
  obtain ⟨v,hv,he⟩ := CoreSemantics132.actual_frame_endpoint
    Endpoint132.unsat p P r hr hP hpair
  have hseven : ([0,10,18,34,66,130,258] : List Nat).all
      (fun w => decide (w ∈ nbrs 2)) = true := by decide +kernel
  have hvnbr : v ∈ nbrs 2 :=
    of_decide_eq_true (List.all_eq_true.mp hseven v hv)
  have heven : ∀ j : Fin 4,
      (winOf [0,1,2,0,3,2]).getD (2*j.val) 0 ∈ nbrs 2 := by decide +kernel
  have hframe : ∀ j, j < 4 →
      amap P (vx p r) (vx p (r+2*j)) ∈ nbrs 2 := by
    intro j hj
    have hw := frame_window p P r (canon_winOf [0,1,2,0,3,2]) hr hP
      (2*j) (by change 2*j ≤ 6; omega)
    rw [← hw]
    exact heven ⟨j,hj⟩
  let z := vx p r ^^^ 2^(P.bwd 1)
  have hz : z < 512 := xor_pow_lt (vx_lt p r) (P.bwd_lt 1 (by decide))
  have hzmap : amap P (vx p r) z = 2 := by
    change amap P (vx p r) (vx p r ^^^ 2^(P.bwd 1)) = 2
    rw [amap_flip P (vx p r) (vx p r) (P.bwd_lt 1 (by decide)),
      amap_self,P.fwd_bwd 1 (by decide)]
    rfl
  have hfour : ∀ j, j < 4 → vx p (r+2*j) ∈ nbrs z := by
    intro j hj
    apply pullback_neighbor P (vx p r) z (vx p (r+2*j)) (vx_lt p r) hz (vx_lt p _)
    rw [hzmap]
    exact hframe j hj
  have heindex : ∃ e, (e=0 ∨ e=m) ∧ v = amap P (vx p r) (vx p e) := by
    rcases (frameE_cases p P he).2 with h0 | hm
    · exact ⟨0,Or.inl rfl,h0⟩
    · exact ⟨m,Or.inr rfl,hm⟩
  obtain ⟨e,heindex,hve⟩ := heindex
  have hendpoint : vx p e ∈ nbrs z := by
    apply pullback_neighbor P (vx p r) z (vx p e) (vx_lt p r) hz (vx_lt p e)
    rw [hzmap,← hve]
    exact hvnbr
  have habsent : sel p (fun w => w) z = false := by
    cases hs : sel p (fun w => w) z with
    | false => rfl
    | true =>
      obtain ⟨i,hi,heq⟩ := (sel_iff p (fun w => w) z).mp hs
      change vx p i = z at heq
      have h0 : vx p r ∈ nbrs (vx p i) := by
        rw [heq]
        simpa using hfour 0 (by decide)
      have h6 : vx p (r+6) ∈ nbrs (vx p i) := by
        rw [heq]
        simpa using hfour 3 (by decide)
      have hi0 := (vx_adj_iff p hi (show r ≤ m by omega)).mp ((mem_nbrs _ _).mp h0)
      have hi6 := (vx_adj_iff p hi hr).mp ((mem_nbrs _ _).mp h6)
      exfalso
      omega
  exact ⟨e,z,heindex,hz,habsent,hendpoint,hfour⟩

#print axioms pullback_neighbor
#print axioms actual_common_neighbor
end Snake9.CommonNeighbor134
