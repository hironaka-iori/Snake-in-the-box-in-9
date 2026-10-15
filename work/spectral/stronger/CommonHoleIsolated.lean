import DenseOuterBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

namespace DenseOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DenseOuterConfig p a b c d)
include h

theorem absent_middle_pair (r : Coord) (hra : r≠a) (hrb : r≠b) :
    ¬InPath p (pair a r) := by
  intro hr
  have hza : InPath (translate p (unit a)) (unit a) :=
    (translate_unit_membership p a a).mpr (by simpa only [pair_self] using h.outer.hzero)
  have hzb := (translate_unit_membership p a b).mpr h.outer.hab_selected
  have hz0 : InPath (translate p (unit a)) 0 :=
    (inPath_translate_at p (unit a) 0).mpr (by simpa using h.outer.ha)
  rcases unit_cover_two (translate p (unit a)) a b hz0 hza hzb h.outer.hab r
    ((translate_unit_membership p a r).mpr hr) with he | he
  · exact hra he
  · exact hrb he

theorem row_internal_data (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (hn : ¬AtMostOneNeighbor p (pair b k)) :
    InPath p (triple b k c) ∧ InPath p (triple b k d) ∧
      ¬InPath p (pair c k) ∧ ¬InPath p (quad a b d k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hs := h.active_corners k hk hke
  have ht := force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
    hn (h.row_cover k hk hke)
  refine ⟨ht.1,ht.2,?_,?_⟩
  · intro hc
    apply middle_row_triple_forbidden p a b k c h.outer.hab (Ne.symm hh.1)
      h.outer.hac (Ne.symm hh.2.1) h.outer.hbc hh.2.2.1 hs.1
      (by simpa only [pair_comm c k] using hc)
      (by simpa only [quad_swap_last a b c k] using hs.2.2) ht.1
  · intro hq
    apply middle_row_triple_forbidden p a b k d h.outer.hab (Ne.symm hh.1)
      h.outer.had (Ne.symm hh.2.1) h.outer.hbd hh.2.2.2 hs.1
      (by simpa only [pair_comm d k] using hs.2.1)
      (by simpa only [quad_swap_last a b d k] using hq) ht.2

theorem isolated_saturation (f : MissingAtNeighbor p a b) (k r s : Coord)
    (hk : k∈distinctR a b c d) (hr : r∈distinctR a b c d) (hrk : r≠k)
    (hsa : s≠a) (hsb : s≠b) (hisol : ∀t∈f.F,k∉t) :
    ¬InPath p (quad a k r s) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hh' := (mem_distinctR a b c d r).mp hr
  have hs := h.ordinary_corners k r hk hr (Ne.symm hrk)
  have ht : InPath p (triple a k r) := by
    apply (f.selected_iff k r (Ne.symm hrk) hh.1 hh.2.1 hh'.1 hh'.2.1).mpr
    intro hm; exact hisol _ hm (by simp)
  exact two_layer_saturation p a b k r s h.outer.hab hsa hsb hs.1 hs.2 ht

theorem isolated_c_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
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
    exact False.elim (h.absent_middle_pair k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.absent_middle_pair c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrd : r=d
  · subst r; right; exact quad_swap_last _ _ _ _
  apply False.elim (h.isolated_saturation f k r c hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) hrk
    (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hisol _)
  have he : quad a c k r=quad a k r c := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw

theorem isolated_d_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
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
    exact False.elim (h.absent_middle_pair k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.absent_middle_pair d (Ne.symm h.outer.had) (Ne.symm h.outer.hbd) hw)
  by_cases hrb : r=b
  · subst r
    apply False.elim (hnq _)
    have he : quad a d k b=quad a b d k := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hw
  by_cases hrc : r=c
  · subst r; right; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  apply False.elim (h.isolated_saturation f k r d hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) hrk
    (Ne.symm h.outer.had) (Ne.symm h.outer.hbd) hisol _)
  have he : quad a d k r=quad a k r d := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw

theorem isolated_endpoint_group (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (hisol : ∀s∈f.F,k∉s) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) ∨
      AtMostOneNeighbor p (triple a d k) := by
  by_contra hn
  push_neg at hn
  have hh := (mem_distinctR a b c d k).mp hk
  have hs := h.active_corners k hk hke
  have ht := h.active_middle_selected f k hk hisol
  have hr := h.row_internal_data k hk hke hn.1
  have hq := (force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
    hn.2.1 (h.isolated_c_cover f k hk hisol hr.2.2.1)).2
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
  · exact (translate_pair_membership p a c k).mpr ht.1
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hq
  · exact (translate_pair_membership p a d k).mpr ht.2
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hs.2.1
  · apply (inPath_translate_at p (unit a) _).mpr
    have ht' : InPath p (triple b d k) := by simpa only [triple_swap b k d] using hr.2.1
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using ht'

end DenseOuterConfig
#print axioms DenseOuterConfig.isolated_endpoint_group
end
end Snake9
