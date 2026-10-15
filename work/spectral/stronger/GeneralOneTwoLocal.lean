import OneTwoLocal
import EndpointGeometry
import GeneralMissingFamily

namespace Snake9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem selected_has_neighbor {m : Nat} (p : Snake m) (hm : 1≤m)
    {v : Vertex} (hv : InPath p v) : ∃w, InPath p w ∧ Adj v w := by
  obtain ⟨i,rfl⟩ := hv
  by_cases hi : i.val=0
  · refine ⟨p.vertex ⟨1,by omega⟩,⟨⟨1,by omega⟩,rfl⟩,?_⟩
    exact (path_adj_iff p _ _).mpr (Or.inl (by simpa [hi]))
  · refine ⟨p.vertex ⟨i.val-1,by omega⟩,⟨⟨i.val-1,by omega⟩,rfl⟩,?_⟩
    exact (path_adj_iff p _ _).mpr (Or.inr (by simp only; omega))

theorem triple_forbidden_two_pairs_quad {m : Nat} (p : Snake m)
    (a x y z : Coord) (hax : a≠x) (hay : a≠y) (haz : a≠z) (hxy : x≠y)
    (hx : InPath p (pair x z)) (hy : InPath p (pair y z))
    (hq : InPath p (quad a x y z)) : ¬ InPath p (triple x y z) := by
  intro ht
  have hadjx : Adj (triple x y z) (pair x z) := by
    rw [triple_swap x y z]; exact adj_symmetric (pair_triple_adj _ _ _)
  have hadjy : Adj (triple x y z) (pair y z) := by
    have he : triple x y z=triple y z x := by
      apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
    rw [he]; exact adj_symmetric (pair_triple_adj _ _ _)
  have hadjq : Adj (triple x y z) (quad a x y z) := by
    have he : quad a x y z=quad x y z a := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rw [he]; exact triple_quad_adj _ _ _ _
  rcases selected_three_neighbors_repeat p ht hx hy hq hadjx hadjy hadjq with he | he | he
  · rw [pair_comm x z,pair_comm y z] at he
    exact hxy (pair_injective_right z x y he)
  · have hb := congrArg (fun q : Vertex => q.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm hax,Ne.symm hay,Ne.symm haz] at hb
  · have hb := congrArg (fun q : Vertex => q.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm hax,Ne.symm hay,Ne.symm haz] at hb

namespace OneTwoRoot
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OneTwoRoot p a b c d)
include h

theorem length_pos : 1≤m := by
  obtain ⟨i,hi⟩ := h.ha
  obtain ⟨j,hj⟩ := h.hb
  by_contra hn
  have hij : i=j := Fin.ext (by have hi := i.isLt; have hj := j.isLt; omega)
  apply h.hab
  exact unit_injective a b (hi.symm.trans ((congrArg p.vertex hij).trans hj))

theorem ordinary_pair_neighbors (i j : Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hja : j≠a) (hjb : j≠b) (hjc : j≠c) (hjd : j≠d) (hij : i≠j) :
    ∀w, InPath p w → Adj (pair i j) w → w=triple a i j ∨ w=triple b i j := by
  have hp : InPath p (pair i j) := by
    apply h.selected_pair i j hij hia hib hja hjb
    simp [hic,hid]
  intro w hw hadj
  obtain ⟨k,rfl⟩ := neighbor_pair i j hadj
  by_cases hki : k=i
  · subst k
    rw [triple_cancel_left] at hw
    exact False.elim (h.absent_unit j hja hjb hw)
  by_cases hkj : k=j
  · subst k
    rw [triple_cancel_right] at hw
    exact False.elim (h.absent_unit i hia hib hw)
  by_cases hka : k=a
  · subst k
    exact Or.inl (triple_rotate i j a)
  by_cases hkb : k=b
  · subst k
    exact Or.inr (triple_rotate i j b)
  have hik : InPath p (pair i k) := by
    apply h.selected_pair i k (Ne.symm hki) hia hib hka hkb
    simp [hic,hid]
  have hjk : InPath p (pair j k) := by
    apply h.selected_pair j k (Ne.symm hkj) hja hjb hka hkb
    simp [hjc,hjd]
  exact False.elim (selected_triple_forbidden p i j k hij (Ne.symm hki) (Ne.symm hkj) hp hik hjk hw)

theorem missing_ordinary_connection_false (i j : Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hja : j≠a) (hjb : j≠b) (hjc : j≠c) (hjd : j≠d) (hij : i≠j)
    (hq : InPath p (quad a b i j))
    (hti : InPath p (triple a b i)) (htj : InPath p (triple a b j))
    (haij : ¬ InPath p (triple a i j)) : False := by
  have hbij := quad_two_rows_excludes_side p a b i j h.hab (Ne.symm hia) (Ne.symm hja) hij hq hti htj
  have hp : InPath p (pair i j) := by
    apply h.selected_pair i j hij hia hib hja hjb
    simp [hic,hid]
  obtain ⟨w,hw,hadj⟩ := selected_has_neighbor p h.length_pos hp
  rcases h.ordinary_pair_neighbors i j hia hib hic hid hja hjb hjc hjd hij w hw hadj with he | he
  · exact haij (he ▸ hw)
  · exact hbij (he ▸ hw)

theorem isolated_neighbor_pair_group (f : MissingAtNeighbor p a c)
    (i : Coord) (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hd : ∀s∈f.F,d∉s) (hi : ∀s∈f.F,i∉s) :
    AtMostOneNeighbor p (pair c i) ∨ AtMostOneNeighbor p (triple a d i) := by
  have hsel (x y : Coord) (hxy : x≠y) (hxa : x≠a) (hxc : x≠c)
      (hya : y≠a) (hyc : y≠c) (hx : ∀s∈f.F,x∉s) : InPath p (triple a x y) := by
    apply (f.selected_iff x y hxy hxa hxc hya hyc).mpr
    intro hm
    exact hx _ hm (by simp)
  have hadi := hsel d i (Ne.symm hid) (Ne.symm h.had) (Ne.symm h.hcd) hia hic hd
  have hcvr : ∀w, InPath p w → Adj (triple a d i) w →
      w=pair d i ∨ w=quad a c d i := by
    intro w hw hadj
    obtain ⟨k,rfl⟩ := neighbor_triple a d i hadj
    by_cases hka : k=a
    · subst k; exact Or.inl (quad_cancel_first _ _ _)
    by_cases hkd : k=d
    · subst k; rw [quad_cancel_second] at hw
      exact False.elim (h.absent_pair_ak i hia hic hw)
    by_cases hki : k=i
    · subst k; rw [quad_cancel_third] at hw
      exact False.elim (h.absent_pair_ak d (Ne.symm h.had) (Ne.symm h.hcd) hw)
    by_cases hkc : k=c
    · subst k; right
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    have hadk := hsel d k (Ne.symm hkd) (Ne.symm h.had) (Ne.symm h.hcd) hka hkc hd
    have haik := hsel i k (Ne.symm hki) hia hic hka hkc hi
    exact False.elim (ordinary_quad_absent p a d i k h.had hid hkd (Ne.symm hki)
      hadi hadk haik hw)
  by_contra hn
  push_neg at hn
  have hq := (force_two_neighbors p (triple a d i) (pair d i) (quad a c d i) hn.2 hcvr).2
  have hci : InPath p (pair c i) := by
    apply h.selected_pair c i (Ne.symm hic) (Ne.symm h.hac) (Ne.symm h.hbc) hia hib
    simp [h.hcd,hid]
  have hdi : InPath p (pair d i) := by
    apply h.selected_pair d i (Ne.symm hid) (Ne.symm h.had) (Ne.symm h.hbd) hia hib
    simp [Ne.symm h.hcd,hic]
  have hmisscdi := triple_forbidden_two_pairs_quad p a c d i h.hac h.had (Ne.symm hia)
    h.hcd hci hdi hq
  have hccvr : ∀w, InPath p w → Adj (pair c i) w → w=triple a c i ∨ w=triple b c i := by
    intro w hw hadj
    rcases exception_row_cover p a b c d i (Ne.symm h.hac) (Ne.symm h.hbc)
      h.hcd hia hib hic hid h.cover h.forced w hw hadj with he | he | he
    · exact Or.inl he
    · exact Or.inr he
    · exact False.elim (hmisscdi (he ▸ hw))
  have haci := (force_two_neighbors p (pair c i) (triple a c i) (triple b c i) hn.1 hccvr).1
  have hq' : InPath p (quad d a i c) := by
    have he : quad a c d i=quad d a i c := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hq
  have hci' : InPath p (pair i c) := by simpa only [pair_comm c i] using hci
  have hz := triple_forbidden_two_pairs_quad p d a i c (Ne.symm h.had) (Ne.symm hid)
    (Ne.symm h.hcd) (Ne.symm hia) h.hac_selected hci' hq'
  apply hz
  simpa only [triple_swap a c i] using haci

end OneTwoRoot
#print axioms OneTwoRoot.missing_ordinary_connection_false
#print axioms OneTwoRoot.isolated_neighbor_pair_group
end Snake9
