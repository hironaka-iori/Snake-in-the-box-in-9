import CubeLocal
import SquareCounterexample

namespace Snake9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem selected_triple_forbidden {m : Nat} (p : Snake m)
    (i j k : Coord) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hpij : InPath p (pair i j)) (hpik : InPath p (pair i k))
    (hpjk : InPath p (pair j k)) : ¬ InPath p (triple i j k) := by
  intro ht
  have ha := triple_adj_sides i j k
  have hd := three_pairs_distinct i j k hij hik hjk
  rcases selected_three_neighbors_repeat p ht hpij hpik hpjk ha.1 ha.2.1 ha.2.2 with h | h | h
  · exact hd.1 h
  · exact hd.2.1 h
  · exact hd.2.2 h

theorem root_internal_arm {m : Nat} (p : Snake m) (hm : 3≤m) (h0 : InPath p 0) :
    ∃ a i : Coord, a≠i ∧ InPath p (unit a) ∧ InPath p (pair a i) ∧ ¬ InPath p (unit i) := by
  obtain ⟨r,hr⟩ := h0
  obtain ⟨s,hs0,hsm,hrs⟩ := exists_internal_neighbor p hm r
  have hs : Adj 0 (p.vertex s) := by rw [← hr]; exact hrs
  obtain ⟨a,ha⟩ := (adj_zero_iff _).mp hs
  obtain ⟨t,htr,hst⟩ := internal_other_neighbor p s r hs0 hsm
  have hc : Adj (unit a) (p.vertex t) := by rw [← ha]; exact hst
  obtain ⟨i,hi⟩ := neighbor_unit a hc
  have ht0 : p.vertex t ≠ 0 := fun h => htr (p.distinct t r (h.trans hr.symm))
  have hai : a≠i := by
    intro he
    subst i
    exact ht0 (hi.trans (pair_self a))
  refine ⟨a,i,hai,⟨s,ha⟩,⟨t,hi⟩,?_⟩
  intro hui
  exact selected_no_four_cycle p ⟨r,hr⟩ ⟨s,ha⟩ ⟨t,hi⟩ hui
    ((adj_zero_iff _).mpr ⟨a,rfl⟩) (unit_pair_adj a i)
    (by rw [pair_comm a i]; exact adj_symmetric (unit_pair_adj i a))
    (adj_symmetric ((adj_zero_iff _).mpr ⟨i,rfl⟩))
    (Ne.symm (pair_nonzero a i hai)) (fun h => hai (unit_injective a i h))

theorem root_unit_cover {m : Nat} (p : Snake m) (h0 : InPath p 0)
    (a i : Coord) (ha : InPath p (unit a)) (hi : ¬ InPath p (unit i)) :
    ∃ b : Coord, b≠a ∧ b≠i ∧ ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b := by
  classical
  by_cases he : ∃ b : Coord, b≠a ∧ InPath p (unit b)
  · obtain ⟨b,hba,hb⟩ := he
    refine ⟨b,hba,(fun h => hi (h ▸ hb)),?_⟩
    intro k hk
    rcases selected_three_neighbors_repeat p h0 ha hb hk
      ((adj_zero_iff _).mpr ⟨a,rfl⟩) ((adj_zero_iff _).mpr ⟨b,rfl⟩)
      ((adj_zero_iff _).mpr ⟨k,rfl⟩) with h | h | h
    · exact False.elim (hba (unit_injective a b h).symm)
    · exact Or.inl (unit_injective a k h).symm
    · exact Or.inr (unit_injective b k h).symm
  · let b := freshCoords a a i 0
    have hb := (freshCoords_spec a a i).1 0
    refine ⟨b,hb.1,hb.2.2,?_⟩
    intro k hk
    by_cases hka : k=a
    · exact Or.inl hka
    · exact False.elim (he ⟨k,hka,hk⟩)

def ForcedPairs {m : Nat} (p : Snake m) : Prop :=
  ∀ i j : Coord, i≠j → ¬ InPath p (unit i) → ¬ InPath p (unit j) → InPath p (pair i j)

theorem missing_candidate_low_degree {m : Nat} (p : Snake m)
    (a b i j : Coord) (hia : i≠a) (hib : i≠b) (hja : j≠a) (hjb : j≠b) (hij : i≠j)
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedPairs p) (missing : ¬ InPath p (triple a i j)) :
    AtMostOneNeighbor p (pair i j) := by
  have absent (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬ InPath p (unit k) := by
    intro hk
    rcases cover k hk with h | h
    · exact hka h
    · exact hkb h
  have unique (v : Vertex) (hv : InPath p v) (hadj : Adj (pair i j) v) : v=triple i j b := by
    obtain ⟨k,rfl⟩ := neighbor_pair i j hadj
    by_cases hki : k=i
    · subst k
      rw [triple_cancel_left] at hv
      exact False.elim (absent j hja hjb hv)
    by_cases hkj : k=j
    · subst k
      rw [triple_cancel_right] at hv
      exact False.elim (absent i hia hib hv)
    by_cases hka : k=a
    · subst k
      rw [triple_rotate] at hv
      exact False.elim (missing hv)
    by_cases hkb : k=b
    · exact congrArg (triple i j) hkb
    exact False.elim (selected_triple_forbidden p i j k hij (Ne.symm hki) (Ne.symm hkj)
      (forced i j hij (absent i hia hib) (absent j hja hjb))
      (forced i k (Ne.symm hki) (absent i hia hib) (absent k hka hkb))
      (forced j k (Ne.symm hkj) (absent j hja hjb) (absent k hka hkb)) hv)
  intro v w hv hw hadjv hadjw
  exact (unique v hv hadjv).trans (unique w hw hadjw).symm

theorem forced_pairs_impossible {m : Nat} (p : Snake m) (hm : 3≤m)
    (h0 : InPath p 0) (forced : ForcedPairs p) : False := by
  obtain ⟨a,i,hai,ha,hc,hi⟩ := root_internal_arm p hm h0
  obtain ⟨b,hba,hbi,cover⟩ := root_unit_cover p h0 a i ha hi
  let j := freshCoords a b i
  have outside := (freshCoords_spec a b i).1
  have distinct := (freshCoords_spec a b i).2
  have absent (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬ InPath p (unit k) := by
    intro hk
    rcases cover k hk with h | h
    · exact hka h
    · exact hkb h
  apply four_candidates_impossible p (fun k => pair i (j k)) (fun k => triple a i (j k))
  · intro k
    exact forced i (j k) (Ne.symm (outside k).2.2) hi
      (absent (j k) (outside k).1 (outside k).2.1)
  · intro k l h
    exact distinct k l (pair_injective_right i (j k) (j l) h)
  · intro k l hk hl
    rcases selected_three_neighbors_repeat p hc ha hk hl
      (adj_symmetric (unit_pair_adj a i)) (pair_triple_adj a i (j k))
      (pair_triple_adj a i (j l)) with h | h | h
    · exact False.elim (triple_ne_unit a i (j k) (Ne.symm (outside k).2.2) h.symm)
    · exact False.elim (triple_ne_unit a i (j l) (Ne.symm (outside l).2.2) h.symm)
    · exact distinct k l (triple_injective_right a i (j k) (j l) h)
  · intro k hk
    exact missing_candidate_low_degree p a b i (j k) (Ne.symm hai) (Ne.symm hbi)
      (outside k).1 (outside k).2.1 (Ne.symm (outside k).2.2) cover forced hk


theorem root_singleton_long {m : Nat} (p : Snake m) (hm : 3≤m) (h0 : InPath p 0) :
    ∃ a b : Coord, a≠b ∧ ¬ InPath p (unit a) ∧ ¬ InPath p (unit b) ∧ ¬ InPath p (pair a b) := by
  classical
  apply Classical.byContradiction
  intro hnone
  apply forced_pairs_impossible p hm h0
  intro a b hab ha hb
  apply Classical.byContradiction
  intro hp
  exact hnone ⟨a,b,hab,ha,hb,hp⟩

def SmallFace (a b : Coord) (v : Vertex) : Prop := v=unit a ∨ v=unit b ∨ v=pair a b

theorem small_faces_nonzero (v : Vertex) :
    (SmallFace 0 1 v ∨ SmallFace 2 3 v ∨ SmallFace 4 5 v) → v≠0 := by
  intro h
  rcases h with h | h | h <;> rcases h with h | h | h <;> subst v <;> decide

theorem small_faces_disjoint (u v : Vertex) :
    (SmallFace 0 1 u → SmallFace 2 3 v → u≠v) ∧
    (SmallFace 0 1 u → SmallFace 4 5 v → u≠v) ∧
    (SmallFace 2 3 u → SmallFace 4 5 v → u≠v) := by
  refine ⟨?_,?_,?_⟩ <;> intro hu hv <;>
    rcases hu with h | h | h <;> rcases hv with h' | h' | h' <;>
    subst u <;> subst v <;> decide

theorem root_singleton_short {m : Nat} (p : Snake m) (hm : m<3) (h0 : InPath p 0) :
    ∃ a b : Coord, a≠b ∧ ¬ InPath p (unit a) ∧ ¬ InPath p (unit b) ∧ ¬ InPath p (pair a b) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have face_hit (a b : Coord) (hab : a≠b) : ∃ v, InPath p v ∧ SmallFace a b v := by
    by_cases ha : InPath p (unit a)
    · exact ⟨unit a,ha,Or.inl rfl⟩
    by_cases hb : InPath p (unit b)
    · exact ⟨unit b,hb,Or.inr (Or.inl rfl)⟩
    by_cases hc : InPath p (pair a b)
    · exact ⟨pair a b,hc,Or.inr (Or.inr rfl)⟩
    exact False.elim (hnone ⟨a,b,hab,ha,hb,hc⟩)
  obtain ⟨u,⟨r,hr⟩,hu⟩ := face_hit 0 1 (by decide)
  obtain ⟨v,⟨s,hs⟩,hv⟩ := face_hit 2 3 (by decide)
  obtain ⟨w,⟨t,ht⟩,hw⟩ := face_hit 4 5 (by decide)
  obtain ⟨z,hz⟩ := h0
  have r0 : r.val ≠ z.val := by
    intro h
    exact small_faces_nonzero u (Or.inl hu) (hr.symm.trans ((congrArg p.vertex (Fin.ext h)).trans hz))
  have s0 : s.val ≠ z.val := by
    intro h
    exact small_faces_nonzero v (Or.inr (Or.inl hv)) (hs.symm.trans ((congrArg p.vertex (Fin.ext h)).trans hz))
  have t0 : t.val ≠ z.val := by
    intro h
    exact small_faces_nonzero w (Or.inr (Or.inr hw)) (ht.symm.trans ((congrArg p.vertex (Fin.ext h)).trans hz))
  have rs : r.val ≠ s.val := by
    intro h
    exact (small_faces_disjoint u v).1 hu hv (hr.symm.trans ((congrArg p.vertex (Fin.ext h)).trans hs))
  have rt : r.val ≠ t.val := by
    intro h
    exact (small_faces_disjoint u w).2.1 hu hw (hr.symm.trans ((congrArg p.vertex (Fin.ext h)).trans ht))
  have st : s.val ≠ t.val := by
    intro h
    exact (small_faces_disjoint v w).2.2 hv hw (hs.symm.trans ((congrArg p.vertex (Fin.ext h)).trans ht))
  omega

theorem root_singleton_exists {m : Nat} (p : Snake m) (h0 : InPath p 0) :
    ∃ a b : Coord, a≠b ∧ ¬ InPath p (unit a) ∧ ¬ InPath p (unit b) ∧ ¬ InPath p (pair a b) := by
  by_cases hm : 3≤m
  · exact root_singleton_long p hm h0
  · exact root_singleton_short p (by omega) h0

theorem singleton_square_exists {m : Nat} (p : Snake m) (i : Fin (m+1)) :
    ∃ a b : Nat, SquareCounterexample.SingletonSquare p i a b := by
  let q := translate p (p.vertex i)
  have h0 : InPath q 0 := ⟨i,vxor_self _⟩
  obtain ⟨a,b,hab,ha,hb,hc⟩ := root_singleton_exists q h0
  have build (a b : Coord) (hab : a.val<b.val)
      (ha : ¬ InPath q (unit a)) (hb : ¬ InPath q (unit b)) (hc : ¬ InPath q (pair a b)) :
      SquareCounterexample.SingletonSquare p i a.val b.val := by
    refine ⟨a.isLt,b.isLt,hab,?_⟩
    intro j
    have absent (v : Vertex) (h : ¬ InPath q v) : p.vertex j ≠ vxor (p.vertex i) v := by
      intro he
      apply h
      refine ⟨j,?_⟩
      change vxor (p.vertex i) (p.vertex j)=v
      rw [he,vxor_cancel]
    refine ⟨?_,?_,?_⟩
    · intro he
      exact absent (unit a) ha (Fin.ext he)
    · intro he
      exact absent (unit b) hb (Fin.ext he)
    · intro he
      apply absent (pair a b) hc
      apply Fin.ext
      change (p.vertex j).val = (p.vertex i).val ^^^ (2^a.val ^^^ 2^b.val)
      change (p.vertex j).val = ((p.vertex i).val ^^^ 2^a.val) ^^^ 2^b.val at he
      rw [Nat.xor_assoc] at he
      exact he
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · exact ⟨a.val,b.val,build a b h ha hb hc⟩
  · exact False.elim (hab (Fin.ext h))
  · exact ⟨b.val,a.val,build b a h hb ha (by rw [pair_comm]; exact hc)⟩

theorem singleton_pairs_positive {m : Nat} (p : Snake m) (i : Fin (m+1)) :
    1 ≤ (SquareCounterexample.singletonPairs p i).length := by
  obtain ⟨a,b,h⟩ := singleton_square_exists p i
  have hm := (SquareCounterexample.mem_singletonPairs_iff p i a b).mpr h
  have hl := List.length_pos_of_mem hm
  omega

#print axioms singleton_square_exists
#print axioms singleton_pairs_positive
#print axioms forced_pairs_impossible
end Snake9
