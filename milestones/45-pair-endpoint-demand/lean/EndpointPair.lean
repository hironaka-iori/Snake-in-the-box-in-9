import LocalWindowSat.EndpointPair451
import LocalWindowUnsat.EndpointPair451
import JointCountBridge
import LocalWindowDirBridge

namespace Snake9.LocalWindow.EndpointPair451
set_option maxHeartbeats 0
def directions : List Nat := [0,1,2,3,4,0,3,1]

theorem endpoint_in_frame {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+8 ≤ m)
    (hP : ∀ j, j<8 → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hsmall : coreAlpha p (r+2)+coreAlpha p (r+6) ≤ 7) :
    ∃ v ∈ endpointVertices, frameE p P (vx p r) v = true := by
  classical
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have hb : ∀ i, i<bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2 := by
    intro i hi
    have hi7 : i<7 := by simpa [bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simpa [bounds] using hu
  have ax := frame_axioms p P r hc (by decide) hr hP hb
  have h2 := JointTags.frame_count p P r hc hr hP 1 (by decide)
  have c2v : window.getD 2 0 = centre2.v := by decide +kernel
  have c2a : dirOfStep (window.getD 1 0) (window.getD 2 0) = centre2.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c2b : dirOfStep (window.getD 2 0) (window.getD 3 0) = centre2.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c2a,c2b,c2v] at h2
  rw [show r+1+1=r+2 by omega] at h2
  have h6 := JointTags.frame_count p P r hc hr hP 5 (by decide)
  have c6v : window.getD 6 0 = centre6.v := by decide +kernel
  have c6a : dirOfStep (window.getD 5 0) (window.getD 6 0) = centre6.d₁ := by rw [Tags.dirOfStep_eq]; decide +kernel
  have c6b : dirOfStep (window.getD 6 0) (window.getD 7 0) = centre6.d₂ := by rw [Tags.dirOfStep_eq]; decide +kernel
  rw [c6a,c6b,c6v] at h6
  rw [show r+5+1=r+6 by omega] at h6
  have hj : jointSum (sel p (amap P (vx p r))) ≤ 7 := by
    unfold jointSum
    rw [h2,h6]
    exact hsmall
  by_contra hn
  have hnone : ∀ v ∈ endpointVertices, frameE p P (vx p r) v = false := by
    intro v hv
    cases he : frameE p P (vx p r) v with
    | false => rfl
    | true => exact False.elim (hn ⟨v,hv,he⟩)
  obtain ⟨τ,hτ⟩ := sat _ _ ax hj hnone
  rw [unsat τ] at hτ
  exact Bool.false_ne_true hτ

def endpointPairs : List (Nat × Nat) :=
  [(0,3),(0,5),(3,5),(4,5),(0,6),(3,6),(4,6),(5,6),
   (0,7),(3,7),(4,7),(5,7),(6,7),(0,8),(3,8),(4,8),(5,8),(6,8),(7,8)]

theorem endpoint_pair {v : Nat} (hv : v ∈ endpointVertices) :
    ∃ a b : Nat, a<9 ∧ b<9 ∧ a≠b ∧ v = (3 ^^^ 2^a) ^^^ 2^b := by
  have hm : endpointVertices = endpointPairs.map (fun q => (3 ^^^ 2^q.1) ^^^ 2^q.2) := by decide +kernel
  have hh : endpointPairs.all (fun q => decide (q.1<9 ∧ q.2<9 ∧ q.1≠q.2)) = true := by decide +kernel
  rw [hm] at hv
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
  have hq' := of_decide_eq_true (List.all_eq_true.mp hh q hq)
  exact ⟨q.1,q.2,hq'.1,hq'.2.1,hq'.2.2,rfl⟩

theorem pullback_two_flips (P : CPerm) (t c z a b : Nat)
    (ht : t<512) (hc : c<512) (hz : z<512)
    (ha : a<9) (hb : b<9) (hab : a≠b)
    (he : amap P t z = (amap P t c ^^^ 2^a) ^^^ 2^b) :
    ∃ u v : Nat, u<9 ∧ v<9 ∧ u≠v ∧ z=(c ^^^ 2^u) ^^^ 2^v := by
  have hu := P.bwd_lt a ha
  have hv := P.bwd_lt b hb
  have huv : P.bwd a ≠ P.bwd b := by
    intro h
    have h' := congrArg P.fwd h
    rw [P.fwd_bwd a ha,P.fwd_bwd b hb] at h'
    exact hab h'
  refine ⟨P.bwd a,P.bwd b,hu,hv,huv,?_⟩
  apply amap_inj P ht hz (xor_pow_lt (xor_pow_lt hc hu) hv)
  rw [amap_flip P t _ hv,amap_flip P t _ hu,P.fwd_bwd a ha,P.fwd_bwd b hb]
  exact he

theorem endpoint_two_flips {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+8 ≤ m)
    (hP : ∀ j, j<8 → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hsmall : coreAlpha p (r+2)+coreAlpha p (r+6) ≤ 7) :
    ∃ k : Nat, (k=0 ∨ k=m) ∧ ∃ u v : Nat,
      u<9 ∧ v<9 ∧ u≠v ∧ vx p k=(vx p (r+2) ^^^ 2^u) ^^^ 2^v := by
  obtain ⟨z,hz,he⟩ := endpoint_in_frame p P r hr hP hsmall
  obtain ⟨a,b,ha,hb,hab,hz'⟩ := endpoint_pair hz
  have hc : Canon window directions := ⟨rfl,rfl,by decide⟩
  have hc2 : 3 = amap P (vx p r) (vx p (r+2)) := by
    simpa [window] using frame_window p P r hc hr hP 2 (by decide)
  have hends := (frameE_cases p P he).2
  rcases hends with he | he
  · refine ⟨0,Or.inl rfl,?_⟩
    apply pullback_two_flips P (vx p r) (vx p (r+2)) (vx p 0) a b
      (vx_lt p r) (vx_lt p (r+2)) (vx_lt p 0) ha hb hab
    rw [← he,← hc2]
    exact hz'
  · refine ⟨m,Or.inr rfl,?_⟩
    apply pullback_two_flips P (vx p r) (vx p (r+2)) (vx p m) a b
      (vx_lt p r) (vx_lt p (r+2)) (vx_lt p m) ha hb hab
    rw [← he,← hc2]
    exact hz'

theorem nearby_endpoint {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j<8 → dir p (r+j) = ([a,b,c,d,e,a,d,b] : List Nat).getD j 0)
    (hsmall : coreAlpha p (r+2)+coreAlpha p (r+6) ≤ 7) :
    ∃ k : Nat, (k=0 ∨ k=m) ∧ ∃ u v : Nat,
      u<9 ∧ v<9 ∧ u≠v ∧ vx p k=(vx p (r+2) ^^^ 2^u) ^^^ 2^v := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply endpoint_two_flips p (mkPerm [a,b,c,d,e]) r hr ?_ hsmall
  intro j hj
  rw [hd j hj]
  interval_cases j
  · exact hs 0 (by simp)
  · exact hs 1 (by simp)
  · exact hs 2 (by simp)
  · exact hs 3 (by simp)
  · exact hs 4 (by simp)
  · exact hs 0 (by simp)
  · exact hs 3 (by simp)
  · exact hs 1 (by simp)

#print axioms endpoint_in_frame
#print axioms endpoint_pair
#print axioms pullback_two_flips
#print axioms endpoint_two_flips
#print axioms nearby_endpoint
end Snake9.LocalWindow.EndpointPair451
