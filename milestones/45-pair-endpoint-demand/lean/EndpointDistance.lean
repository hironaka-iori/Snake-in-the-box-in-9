import EndpointPair
import WitnessSharp

namespace Snake9.LocalWindow.EndpointPair451
set_option maxHeartbeats 0

def hamming (u v : Nat) : Nat :=
  (List.range 9).countP (fun k => (u ^^^ v).testBit k)

theorem two_flips_distance (c a b : Nat) (ha : a<9) (hb : b<9) (hab : a≠b) :
    hamming c ((c ^^^ 2^a) ^^^ 2^b) = 2 := by
  have ht : ∀ a b : Fin 9, a≠b → hamming 0 (2^a.val ^^^ 2^b.val) = 2 := by decide +kernel
  have hf : (⟨a,ha⟩ : Fin 9) ≠ ⟨b,hb⟩ := by intro h; exact hab (congrArg Fin.val h)
  have hx := ht ⟨a,ha⟩ ⟨b,hb⟩ hf
  simpa [hamming,Nat.xor_assoc] using hx

theorem endpoint_at_distance_two {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j<8 → dir p (r+j) = ([a,b,c,d,e,a,d,b] : List Nat).getD j 0)
    (hsmall : coreAlpha p (r+2)+coreAlpha p (r+6) ≤ 7) :
    hamming (vx p (r+2)) (vx p 0) = 2 ∨ hamming (vx p (r+2)) (vx p m) = 2 := by
  obtain ⟨k,hk,u,v,hu,hv,huv,he⟩ := nearby_endpoint p r a b c d e hn h9 hr hd hsmall
  have hh : hamming (vx p (r+2)) (vx p k) = 2 := by
    rw [he]
    exact two_flips_distance _ u v hu hv huv
  rcases hk with rfl | rfl
  · exact Or.inl hh
  · exact Or.inr hh

theorem away_from_endpoints_sum {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j<8 → dir p (r+j) = ([a,b,c,d,e,a,d,b] : List Nat).getD j 0)
    (h0 : 3 ≤ hamming (vx p (r+2)) (vx p 0))
    (hm : 3 ≤ hamming (vx p (r+2)) (vx p m)) :
    8 ≤ coreAlpha p (r+2)+coreAlpha p (r+6) := by
  by_contra! h
  have he := endpoint_at_distance_two p r a b c d e hn h9 hr hd (by omega)
  rcases he with he | he <;> omega

theorem radius_one_insufficient :
    coreAlpha Snake9.ExteriorTurn.Sharp.witness 4 + coreAlpha Snake9.ExteriorTurn.Sharp.witness 8 = 7 ∧
    hamming (vx Snake9.ExteriorTurn.Sharp.witness 4) (vx Snake9.ExteriorTurn.Sharp.witness 0) = 2 ∧
    hamming (vx Snake9.ExteriorTurn.Sharp.witness 4) (vx Snake9.ExteriorTurn.Sharp.witness 140) = 4 := by
  decide +kernel

#print axioms two_flips_distance
#print axioms endpoint_at_distance_two
#print axioms away_from_endpoints_sum
#print axioms radius_one_insufficient
end Snake9.LocalWindow.EndpointPair451
