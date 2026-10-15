import CommonHolePairs

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

namespace CommonHoleConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : CommonHoleConfig p a b c d)
include h

theorem ordinary_saturation (f : MissingAtNeighbor p a b) (k r s : Coord)
    (hk : k∈distinctR a b c d) (hr : r∈distinctR a b c d) (hrk : r≠k)
    (hsa : s≠a) (hsb : s≠b)
    (hRR : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j → ({i,j}:Finset Coord)∉f.F) :
    ¬InPath p (quad a k r s) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hh' := (mem_distinctR a b c d r).mp hr
  have hs := h.ordinary_corners k r hk hr (Ne.symm hrk)
  have ht := (f.selected_iff k r (Ne.symm hrk) hh.1 hh.2.1 hh'.1 hh'.2.1).mpr
    (hRR k r hk hr (Ne.symm hrk))
  exact two_layer_saturation p a b k r s h.outer.hab hsa hsb hs.1 hs.2 ht

theorem ordinary_c_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hRR : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j → ({i,j}:Finset Coord)∉f.F)
    (hnc : ¬InPath p (pair c k)) :
    ∀w, InPath p w → Adj (triple a c k) w →
      w=quad a b c k ∨ w=quad a c d k := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a c k hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw; exact False.elim (hnc hw)
  by_cases hrc : r=c
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.toDense.absent_middle_pair k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.toDense.absent_middle_pair c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrd : r=d
  · subst r; right; exact quad_swap_last _ _ _ _
  apply False.elim (h.ordinary_saturation f k r c hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) hrk
    (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hRR _)
  have he : quad a c k r=quad a k r c := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw

theorem ordinary_d_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hRR : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j → ({i,j}:Finset Coord)∉f.F)
    (hnq : ¬InPath p (quad a b d k)) :
    ∀w, InPath p w → Adj (triple a d k) w →
      w=pair d k ∨ w=quad a c d k := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a d k hadj
  by_cases hra : r=a
  · subst r; left; exact quad_cancel_first _ _ _
  by_cases hrd : r=d
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.toDense.absent_middle_pair k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.toDense.absent_middle_pair d (Ne.symm h.outer.had) (Ne.symm h.outer.hbd) hw)
  by_cases hrb : r=b
  · subst r
    apply False.elim (hnq _)
    have he : quad a d k b=quad a b d k := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hw
  by_cases hrc : r=c
  · subst r; right; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  apply False.elim (h.ordinary_saturation f k r d hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) hrk
    (Ne.symm h.outer.had) (Ne.symm h.outer.hbd) hRR _)
  have he : quad a d k r=quad a k r d := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw

theorem missing_d_pair_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hm : ({d,k}:Finset Coord)∈f.F) :
    ∀w, InPath p w → Adj (pair d k) w → w=triple b d k ∨ w=triple c d k := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair d k hadj
  by_cases hrd : r=d
  · subst r; rw [triple_cancel_left] at hw
    exact False.elim (h.outer.absent_unit k hka hkc hw)
  by_cases hrk : r=k
  · subst r; rw [triple_cancel_right] at hw
    exact False.elim (h.outer.absent_unit d (Ne.symm h.outer.had) (Ne.symm h.outer.hcd) hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw
    exact False.elim ((f.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
      (Ne.symm h.outer.hbd) hka hkb).mp hw hm)
  by_cases hrb : r=b
  · subst r; left; exact triple_rotate _ _ _
  by_cases hrc : r=c
  · subst r; right; exact triple_rotate _ _ _
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  exact False.elim (selected_triple_forbidden p d k r (Ne.symm hkd) (Ne.symm hrd)
    (Ne.symm hrk) (h.side_pair k hk) (h.side_pair r hr)
    (h.ordinary_corners k r hk hr (Ne.symm hrk)).1 hw)

theorem missing_d_endpoint_group (f : MissingAtNeighbor p a b)
    (hRR : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j → ({i,j}:Finset Coord)∉f.F)
    (hCD : ({c,d}:Finset Coord)∉f.F) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (hc : ({c,k}:Finset Coord)∉f.F) (hd : ({d,k}:Finset Coord)∈f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) ∨
      AtMostOneNeighbor p (pair d k) := by
  by_contra hn
  push_neg at hn
  have hh := (mem_distinctR a b c d k).mp hk
  have hs := h.active_corners k hk hke
  have hr := h.toDense.row_internal_data k hk hke hn.1
  have ht := (f.selected_iff c k (Ne.symm hh.2.2.1) (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) hh.1 hh.2.1).mpr hc
  have hacd := (f.selected_iff c d h.outer.hcd (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)).mpr hCD
  have hq := (force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
    hn.2.1 (h.ordinary_c_cover f k hk hRR hr.2.2.1)).2
  have hcdk := (force_two_neighbors p (pair d k) (triple b d k) (triple c d k)
    hn.2.2 (h.missing_d_pair_cover f k hk hd)).2
  have hno := ordinary_quad_absent p c a d k (Ne.symm h.outer.hac)
    (Ne.symm h.outer.had) hh.1 (Ne.symm hh.2.2.2)
    (by simpa only [triple,pair_comm c a] using hacd)
    (by simpa only [triple,pair_comm c a] using ht) hcdk
  apply hno
  simpa only [quad_swap_first a c d k] using hq

theorem missing_c_endpoint_group (f : MissingAtNeighbor p a b)
    (hRR : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j → ({i,j}:Finset Coord)∉f.F)
    (hCD : ({c,d}:Finset Coord)∉f.F) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (hc : ({c,k}:Finset Coord)∈f.F) (hd : ({d,k}:Finset Coord)∉f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a d k) ∨
      AtMostOneNeighbor p (quad a b c k) := by
  have hr (i : Coord) : i∈distinctR b a d c ↔ i∈distinctR a b c d := by
    simp only [mem_distinctR]; tauto
  have hRR' : ∀i j,i∈distinctR b a d c → j∈distinctR b a d c → i≠j →
      ({i,j}:Finset Coord)∉f.mirror.F := by
    intro i j hi hj hij
    exact hRR i j ((hr i).mp hi) ((hr j).mp hj) hij
  have hCD' : ({d,c}:Finset Coord)∉f.mirror.F := by
    change ({d,c}:Finset Coord)∉f.F
    simpa only [Finset.pair_comm d c] using hCD
  rcases h.mirror.missing_d_endpoint_group f.mirror hRR' hCD' k
    ((hr k).mpr hk) hke hd hc with hl | hl | hl
  · left
    have ht := low_of_translate p (pair a b) (pair a k) hl
    have he : vxor (pair a b) (pair a k)=pair b k := by
      have he' : quad a b a k=pair b k := by rw [quad_swap_last,quad_cancel_first]
      simpa only [quad,triple,pair,vxor_assoc] using he'
    exact he ▸ ht
  · right; left
    have ht := low_of_translate p (pair a b) (triple b d k) hl
    simpa only [triple,pair,vxor_assoc,vxor_cancel] using ht
  · right; right
    have ht := low_of_translate p (pair a b) (pair c k) hl
    simpa only [quad,triple,pair,vxor_assoc] using ht

theorem both_middle_endpoint_group (f : MissingAtNeighbor p a b)
    (hRR : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j → ({i,j}:Finset Coord)∉f.F)
    (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (hc : ({c,k}:Finset Coord)∉f.F) (hd : ({d,k}:Finset Coord)∉f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) := by
  by_contra hn
  push_neg at hn
  have hh := (mem_distinctR a b c d k).mp hk
  have hs := h.active_corners k hk hke
  have htc := (f.selected_iff c k (Ne.symm hh.2.2.1) (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) hh.1 hh.2.1).mpr hc
  have htd := (f.selected_iff d k (Ne.symm hh.2.2.2) (Ne.symm h.outer.had)
    (Ne.symm h.outer.hbd) hh.1 hh.2.1).mpr hd
  have hr := h.toDense.row_internal_data k hk hke hn.1
  have hq := (force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
    hn.2 (h.ordinary_c_cover f k hk hRR hr.2.2.1)).2
  apply selected_coordinate_cycle8_false (translate p (unit a)) a b c d k
    h.outer.hab h.outer.hac h.outer.had (Ne.symm hh.1) h.outer.hbc h.outer.hbd
    (Ne.symm hh.2.1) h.outer.hcd (Ne.symm hh.2.2.1) (Ne.symm hh.2.2.2)
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hs.1
  · apply (inPath_translate_at p (unit a) _).mpr
    have ht' : InPath p (triple b c k) := by simpa only [triple_swap b k c] using hr.1
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using ht'
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hs.2.2
  · exact (translate_pair_membership p a c k).mpr htc
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hq
  · exact (translate_pair_membership p a d k).mpr htd
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hs.2.1
  · apply (inPath_translate_at p (unit a) _).mpr
    have ht' : InPath p (triple b d k) := by simpa only [triple_swap b k d] using hr.2.1
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using ht'

theorem active_endpoint (f : MissingAtNeighbor p a b)
    (hRR : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j → ({i,j}:Finset Coord)∉f.F)
    (hCD : ({c,d}:Finset Coord)∉f.F) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (hnoBoth : ¬(({c,k}:Finset Coord)∈f.F ∧ ({d,k}:Finset Coord)∈f.F)) :
    ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧
      (v=pair b k ∨ v=triple a c k ∨ v=triple a d k ∨ v=pair d k ∨ v=quad a b c k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hs := h.active_corners k hk hke
  by_cases hd : ({d,k}:Finset Coord)∈f.F
  · have hc : ({c,k}:Finset Coord)∉f.F := fun hc => hnoBoth ⟨hc,hd⟩
    have ht := (f.selected_iff c k (Ne.symm hh.2.2.1) (Ne.symm h.outer.hac)
      (Ne.symm h.outer.hbc) hh.1 hh.2.1).mpr hc
    rcases h.missing_d_endpoint_group f hRR hCD k hk hke hc hd with hl | hl | hl
    · exact ⟨_,hs.1,hl,Or.inl rfl⟩
    · exact ⟨_,ht,hl,Or.inr (Or.inl rfl)⟩
    · exact ⟨_,hs.2.1,hl,Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  by_cases hc : ({c,k}:Finset Coord)∈f.F
  · have ht := (f.selected_iff d k (Ne.symm hh.2.2.2) (Ne.symm h.outer.had)
      (Ne.symm h.outer.hbd) hh.1 hh.2.1).mpr hd
    rcases h.missing_c_endpoint_group f hRR hCD k hk hke hc hd with hl | hl | hl
    · exact ⟨_,hs.1,hl,Or.inl rfl⟩
    · exact ⟨_,ht,hl,Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨_,hs.2.2,hl,Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  · have ht := (f.selected_iff c k (Ne.symm hh.2.2.1) (Ne.symm h.outer.hac)
      (Ne.symm h.outer.hbc) hh.1 hh.2.1).mpr hc
    rcases h.both_middle_endpoint_group f hRR k hk hke hc hd with hl | hl
    · exact ⟨_,hs.1,hl,Or.inl rfl⟩
    · exact ⟨_,ht,hl,Or.inr (Or.inl rfl)⟩

end CommonHoleConfig
#print axioms CommonHoleConfig.ordinary_c_cover
#print axioms CommonHoleConfig.missing_d_endpoint_group
#print axioms CommonHoleConfig.missing_c_endpoint_group
#print axioms CommonHoleConfig.both_middle_endpoint_group
#print axioms CommonHoleConfig.active_endpoint
end
end Snake9
