import AdjacentNeighborhood
import ExceptionRowNeighbors
import CoordinateCycle

namespace Snake9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

structure OneTwoRoot {m : Nat} (p : Snake m) (a b c d : Coord) : Prop where
  hab : a≠b
  hac : a≠c
  hbc : b≠c
  had : a≠d
  hbd : b≠d
  hcd : c≠d
  ha : InPath p (unit a)
  hb : InPath p (unit b)
  hac_selected : InPath p (pair a c)
  cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b
  qcover : ∀ k : Coord, InPath (translate p (unit a)) (unit k) → k=a ∨ k=c
  forced : ForcedPairsExcept p c d

theorem quad_two_selected_excludes_third {m : Nat} (p : Snake m)
    (a b e k : Coord) (hab : a≠b) (hae : a≠e) (hak : a≠k) (hbe : b≠e)
    (hq : InPath p (quad a b e k))
    (ht : InPath p (triple a b k)) (hu : InPath p (triple a e k)) :
    ¬ InPath p (triple b e k) := by
  intro hz
  have he0 : quad a b e k = quad a b k e := quad_swap_last _ _ _ _
  have he1 : quad a b e k = quad a e k b := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  have he2 : quad a b e k = quad b e k a := (quad_rotate _ _ _ _).symm
  have h0 : Adj (quad a b e k) (triple a b k) := by
    rw [he0]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  have h1 : Adj (quad a b e k) (triple a e k) := by
    rw [he1]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  have h2 : Adj (quad a b e k) (triple b e k) := by
    rw [he2]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  rcases selected_three_neighbors_repeat p hq ht hu hz h0 h1 h2 with he | he | he
  · rw [triple_swap a b k,triple_swap a e k] at he
    exact hbe (triple_injective_right a k b e he)
  · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_triple,Ne.symm hab,Ne.symm hae,Ne.symm hak] at hb
  · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_triple,Ne.symm hab,Ne.symm hae,Ne.symm hak] at hb

theorem quad_two_rows_excludes_side {m : Nat} (p : Snake m)
    (a b i j : Coord) (hab : a≠b) (hai : a≠i) (haj : a≠j) (hij : i≠j)
    (hq : InPath p (quad a b i j))
    (hti : InPath p (triple a b i)) (htj : InPath p (triple a b j)) :
    ¬ InPath p (triple b i j) := by
  have heq : quad a b i j = quad a i j b := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  have hz := quad_two_selected_excludes_third p a i j b hai haj hab hij
    (heq ▸ hq) ((triple_swap a b i) ▸ hti) ((triple_swap a b j) ▸ htj)
  intro he
  apply hz
  rw [triple_rotate i j b]
  exact he

theorem ordinary_quad_absent {m : Nat} (p : Snake m)
    (a b i j : Coord) (hab : a≠b) (hib : i≠b) (hjb : j≠b) (hij : i≠j)
    (hti : InPath p (triple a b i)) (htj : InPath p (triple a b j))
    (haij : InPath p (triple a i j)) : ¬ InPath p (quad a b i j) := by
  intro hq
  have h0 : Adj (quad a b i j) (triple a b i) := adj_symmetric (triple_quad_adj _ _ _ _)
  have h1 : Adj (quad a b i j) (triple a b j) := by
    rw [quad_swap_last]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  have h2 : Adj (quad a b i j) (triple a i j) := by
    have he : quad a b i j = quad a i j b := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rw [he]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  rcases selected_three_neighbors_repeat p hq hti htj haij h0 h1 h2 with he | he | he
  · exact hij (triple_injective_right a b i j he)
  · have hb := congrArg (fun v : Vertex => v.val.testBit b.val) he
    simp [bit_triple,hab,hib,hjb] at hb
  · rw [triple_swap a b j,triple_swap a i j] at he
    exact hib (triple_injective_right a j b i he).symm

namespace OneTwoRoot
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OneTwoRoot p a b c d)
include h

theorem absent_unit (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬ InPath p (unit k) := by
  intro hk
  rcases h.cover k hk with he | he
  · exact hka he
  · exact hkb he

theorem selected_pair (i j : Coord) (hij : i≠j)
    (hia : i≠a) (hib : i≠b) (hja : j≠a) (hjb : j≠b)
    (hnot : ¬ ((i=c ∧ j=d) ∨ (i=d ∧ j=c))) : InPath p (pair i j) :=
  h.forced i j hij (h.absent_unit i hia hib) (h.absent_unit j hja hjb) hnot

theorem absent_pair_ak (k : Coord) (hka : k≠a) (hkc : k≠c) :
    ¬ InPath p (pair a k) := by
  intro hk
  rcases h.qcover k ((translate_unit_membership p a k).mpr hk) with he | he
  · exact hka he
  · exact hkc he

theorem absent_pair_bk (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d) :
    ¬ InPath p (pair b k) := by
  intro hk
  rcases arm_coordinate_in_missing p b a c d k (Ne.symm hkb) (Ne.symm hka)
    h.hb hk (fun x hx => (h.cover x hx).symm) h.forced with he | he
  · exact hkc he
  · exact hkd he

theorem triple_neighbor_cover_general (k : Coord)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d) :
    ∀ w, InPath p w → Adj (triple a b k) w →
      w=quad a b c k ∨ ∃ j : Coord,
        j≠a ∧ j≠b ∧ j≠c ∧ j≠k ∧ w=quad a b k j := by
  intro w hw hadj
  obtain ⟨x,rfl⟩ := neighbor_triple a b k hadj
  by_cases hxa : x=a
  · subst x
    rw [quad_cancel_first] at hw
    exact False.elim (h.absent_pair_bk k hka hkb hkc hkd hw)
  by_cases hxb : x=b
  · subst x
    rw [quad_cancel_second] at hw
    exact False.elim (h.absent_pair_ak k hka hkc hw)
  by_cases hxk : x=k
  · subst x
    rw [quad_cancel_third] at hw
    exact False.elim (h.absent_pair_ak b (Ne.symm h.hab) h.hbc hw)
  by_cases hxc : x=c
  · subst x
    exact Or.inl (quad_swap_last _ _ _ _)
  exact Or.inr ⟨x,hxa,hxb,hxc,hxk,rfl⟩

theorem hole_connection_low_degree (e k : Coord)
    (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d) (hek : e≠k)
    (hq : InPath p (quad a b e k))
    (ht : InPath p (triple a b k)) (hu : InPath p (triple a e k)) :
    AtMostOneNeighbor p (pair e k) := by
  have hz := quad_two_selected_excludes_third p a b e k h.hab
    (Ne.symm hea) (Ne.symm hka) (Ne.symm heb) hq ht hu
  exact missing_candidate_low_degree_except p b a c d e k
    heb hea hec hed hkb hka hkc hkd hek
    (fun x hx => (h.cover x hx).symm) h.forced hz

theorem missing_sides_low_degree (i j : Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hja : j≠a) (hjb : j≠b) (hjc : j≠c) (hij : i≠j)
    (haij : ¬ InPath p (triple a i j)) (hbij : ¬ InPath p (triple b i j)) :
    AtMostOneNeighbor p (pair i j) := by
  by_cases hjd : j=d
  · subst j
    have hcover := exception_row_cover p a b d c i (Ne.symm h.had) (Ne.symm h.hbd)
      (Ne.symm h.hcd) hia hib hid hic h.cover (forced_pairs_except_swap p c d h.forced)
    have ha : ¬ InPath p (triple a d i) := by simpa only [triple_swap a d i] using haij
    have hb : ¬ InPath p (triple b d i) := by simpa only [triple_swap b d i] using hbij
    have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair d i) w) : w=triple d c i := by
      rcases hcover w hw hadj with he | he | he
      · exact False.elim (ha (he ▸ hw))
      · exact False.elim (hb (he ▸ hw))
      · exact he
    rw [pair_comm i d]
    intro u v hu hv hadju hadjv
    exact (unique u hu hadju).trans (unique v hv hadjv).symm
  · exact missing_candidate_low_degree_except p b a c d i j
      hib hia hic hid hjb hja hjc hjd hij
      (fun x hx => (h.cover x hx).symm) h.forced hbij

theorem missing_connection_low_degree (i j : Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hja : j≠a) (hjb : j≠b) (hjc : j≠c) (hij : i≠j)
    (hq : InPath p (quad a b i j))
    (hti : InPath p (triple a b i)) (htj : InPath p (triple a b j))
    (haij : ¬ InPath p (triple a i j)) :
    AtMostOneNeighbor p (pair i j) := by
  exact h.missing_sides_low_degree i j hia hib hic hid hja hjb hjc hij haij
    (quad_two_rows_excludes_side p a b i j h.hab (Ne.symm hia) (Ne.symm hja) hij hq hti htj)

theorem cycle_group_low_degree (k : Coord)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d)
    (ht : InPath p (triple a b k)) (hadk : InPath p (triple a d k))
    (hcvr : ∀ w, InPath p w → Adj (triple a b k) w →
      w=quad a b c k ∨ w=quad a b d k) :
    AtMostOneNeighbor p (triple a b k) ∨
      AtMostOneNeighbor p (pair c k) ∨ AtMostOneNeighbor p (pair d k) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hnt,hnc,hnd⟩ := hn
  have hck : InPath p (pair c k) := by
    apply h.selected_pair c k (Ne.symm hkc) (Ne.symm h.hac) (Ne.symm h.hbc) hka hkb
    simp [h.hcd,hkd]
  have hdk : InPath p (pair d k) := by
    apply h.selected_pair d k (Ne.symm hkd) (Ne.symm h.had) (Ne.symm h.hbd) hka hkb
    simp [Ne.symm h.hcd,hkc]
  have htwo := force_two_neighbors p (triple a b k) (quad a b c k) (quad a b d k) hnt hcvr
  have hmissing_bdk : ¬ InPath p (triple b d k) :=
    quad_two_selected_excludes_third p a b d k h.hab h.had (Ne.symm hka) h.hbd
      htwo.2 ht hadk
  have hmissing_ack : ¬ InPath p (triple a c k) := by
    intro hack
    have hadj0 : Adj (triple a c k) (pair a c) := adj_symmetric (pair_triple_adj _ _ _)
    have hadj1 : Adj (triple a c k) (pair c k) := by
      rw [triple_rotate a c k, triple_rotate k a c]
      exact adj_symmetric (pair_triple_adj _ _ _)
    have hadj2 : Adj (triple a c k) (quad a b c k) := by
      have he : quad a b c k = quad a c k b := by
        apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
      rw [he]; exact triple_quad_adj _ _ _ _
    rcases selected_three_neighbors_repeat p hack h.hac_selected hck htwo.1
      hadj0 hadj1 hadj2 with he | he | he
    · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
      simp [bit_pair,Ne.symm h.hac,hka] at hb
    · have hb := congrArg (fun v : Vertex => v.val.testBit b.val) he
      simp [bit_pair,bit_quad,h.hab,Ne.symm h.hbc,hkb] at hb
    · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
      simp [bit_pair,bit_quad,Ne.symm h.hab,Ne.symm h.hac,hka] at hb
  have hdcvr : ∀ w, InPath p w → Adj (pair d k) w →
      w=triple a d k ∨ w=triple c d k := by
    intro w hw hadj
    rcases exception_row_cover p a b d c k (Ne.symm h.had) (Ne.symm h.hbd)
      (Ne.symm h.hcd) hka hkb hkd hkc h.cover
      (forced_pairs_except_swap p c d h.forced) w hw hadj with he | he | he
    · exact Or.inl he
    · exact False.elim (hmissing_bdk (he ▸ hw))
    · right
      exact he.trans (by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl)
  have hccvr : ∀ w, InPath p w → Adj (pair c k) w →
      w=triple b c k ∨ w=triple c d k := by
    intro w hw hadj
    rcases exception_row_cover p a b c d k (Ne.symm h.hac) (Ne.symm h.hbc)
      h.hcd hka hkb hkc hkd h.cover h.forced w hw hadj with he | he | he
    · exact False.elim (hmissing_ack (he ▸ hw))
    · exact Or.inl he
    · exact Or.inr he
  have hd2 := force_two_neighbors p (pair d k) (triple a d k) (triple c d k) hnd hdcvr
  have hc2 := force_two_neighbors p (pair c k) (triple b c k) (triple c d k) hnc hccvr
  exact selected_coordinate_cycle8_false p a b c d k h.hab h.hac h.had (Ne.symm hka)
    h.hbc h.hbd (Ne.symm hkb) h.hcd (Ne.symm hkc) (Ne.symm hkd)
    ht htwo.1 hc2.1 hck hd2.2 hdk hadk htwo.2

end OneTwoRoot
#print axioms quad_two_rows_excludes_side
#print axioms OneTwoRoot.hole_connection_low_degree
#print axioms OneTwoRoot.missing_connection_low_degree
#print axioms OneTwoRoot.cycle_group_low_degree
end Snake9
