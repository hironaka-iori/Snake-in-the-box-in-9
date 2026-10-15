import DenseOuterBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

/-- Ordinary two-dimensional corners are present; no exceptional-row corners are assumed. -/
structure DenseRowConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  outer : DistinctOuterConfig p a b c d
  ordinary_corners : ∀i j,i∈distinctR a b c d → j∈distinctR a b c d → i≠j →
    InPath p (pair i j) ∧ InPath p (quad a b i j)

namespace DenseRowConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DenseRowConfig p a b c d)
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


theorem row_cover (k : Coord) (hk : k∈distinctR a b c d)
    (hbk : InPath p (pair b k)) :
    ∀w,InPath p w → Adj (pair b k) w → w=triple b k c ∨ w=triple b k d := by
  intro w hw hadj
  rcases h.outer.row_neighbor_cover k hk w hw hadj with he | he | ⟨l,hl,hlk,he⟩
  · exact Or.inl he
  · exact Or.inr he
  · have hh := (mem_distinctR a b c d k).mp hk
    have hh' := (mem_distinctR a b c d l).mp hl
    have hs := h.ordinary_corners k l hk hl (Ne.symm hlk)
    exact False.elim (middle_row_triple_forbidden p a b k l h.outer.hab
      (Ne.symm hh.1) (Ne.symm hh'.1) (Ne.symm hh.2.1) (Ne.symm hh'.2.1)
      (Ne.symm hlk) hbk hs.1 hs.2 (he ▸ hw))

theorem isolated_middle_selected (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s) :
    InPath p (triple a c k) ∧ InPath p (triple a d k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  constructor
  · apply (f.selected_iff c k (Ne.symm hkc) (Ne.symm h.outer.hac)
      (Ne.symm h.outer.hbc) hka hkb).mpr
    intro hm; exact hisol _ hm (by simp)
  · apply (f.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
      (Ne.symm h.outer.hbd) hka hkb).mpr
    intro hm; exact hisol _ hm (by simp)

theorem isolated_endpoint_group (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hbk : InPath p (pair b k))
    (hisol : ∀s∈f.F,k∉s) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) ∨
      AtMostOneNeighbor p (triple a d k) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have ht := h.isolated_middle_selected f k hk hisol
  have hr := force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
    hn.1 (h.row_cover k hk hbk)
  have hdk : InPath p (pair d k) := by
    by_contra hndk
    have hnq : ¬InPath p (quad a b d k) := by
      intro hq
      have adj1 : Adj (quad a b d k) (triple a b d) := adj_symmetric (triple_quad_adj _ _ _ _)
      have adj2 : Adj (quad a b d k) (triple a d k) := by
        have he : quad a b d k=quad a d k b := by
          apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
        rw [he]; exact adj_symmetric (triple_quad_adj _ _ _ _)
      have adj3 : Adj (quad a b d k) (triple b k d) := by
        have he : quad a b d k=quad b k d a := by
          apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
        rw [he]; exact adj_symmetric (triple_quad_adj _ _ _ _)
      rcases selected_three_neighbors_repeat p hq h.outer.habd_selected ht.2 hr.2 adj1 adj2 adj3 with he | he | he
      · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
        simp [bit_triple,h.outer.hab,Ne.symm h.outer.hbd,hkb] at hb
      · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
        simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.had,hka] at hb
      · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
        simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.had,hka] at hb
    exact hndk ((force_two_neighbors p (triple a d k) (pair d k) (quad a c d k)
      hn.2.2 (h.isolated_d_cover f k hk hisol hnq)).1)
  have habck : InPath p (quad a b c k) := by
    by_contra hnq
    have hnck : ¬InPath p (pair c k) := by
      intro hck
      have adj1 : Adj (pair c k) (unit c) := adj_symmetric (unit_pair_adj _ _)
      have adj2 : Adj (pair c k) (triple a c k) := by
        have he : triple a c k=triple c k a := by
          apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
        rw [he]; exact pair_triple_adj _ _ _
      have adj3 : Adj (pair c k) (triple b k c) := by
        have he : triple b k c=triple c k b := by
          apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
        rw [he]; exact pair_triple_adj _ _ _
      rcases selected_three_neighbors_repeat p hck h.outer.hc ht.1 hr.1 adj1 adj2 adj3 with he | he | he
      · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
        simp [bit_unit,bit_triple,Ne.symm h.outer.hac,hka] at hb
      · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
        simp [bit_unit,bit_triple,Ne.symm h.outer.hbc,hkb] at hb
      · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
        simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.hac,hka] at hb
    exact hnq ((force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
      hn.2.1 (h.isolated_c_cover f k hk hisol hnck)).1)
  have hnck : ¬InPath p (pair c k) := by
    intro hc
    apply middle_row_triple_forbidden p a b k c h.outer.hab (Ne.symm hka)
      h.outer.hac (Ne.symm hkb) h.outer.hbc hkc hbk
      (by simpa only [pair_comm c k] using hc)
      (by simpa only [quad_swap_last a b c k] using habck) hr.1
  have hq := (force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
    hn.2.1 (h.isolated_c_cover f k hk hisol hnck)).2
  apply selected_coordinate_cycle8_false (translate p (unit a)) a b c d k
    h.outer.hab h.outer.hac h.outer.had (Ne.symm hka) h.outer.hbc h.outer.hbd
    (Ne.symm hkb) h.outer.hcd (Ne.symm hkc) (Ne.symm hkd)
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hbk
  · apply (inPath_translate_at p (unit a) _).mpr
    have ht' : InPath p (triple b c k) := by simpa only [triple_swap b k c] using hr.1
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using ht'
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using habck
  · exact (translate_pair_membership p a c k).mpr ht.1
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hq
  · exact (translate_pair_membership p a d k).mpr ht.2
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hdk
  · apply (inPath_translate_at p (unit a) _).mpr
    have ht' : InPath p (triple b d k) := by simpa only [triple_swap b k d] using hr.2
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using ht'

end DenseRowConfig
#print axioms DenseRowConfig.isolated_endpoint_group
end
end Snake9
