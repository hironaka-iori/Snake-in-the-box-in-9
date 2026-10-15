import SharedCentralMissingExclusion
import SharedCoreEndpoints

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2000000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem ce_de_support (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.e},{d,h.e}}) :
    ∀S∈f.F,S⊆{c,d,h.e,h.x,h.y} := by
  rw [hF]
  intro S hS
  simp only [mem_insert,mem_singleton] at hS
  rcases hS with rfl | rfl <;> simp [Finset.subset_iff]

theorem ce_de_middle_without_e (f : MissingAtNeighbor p a b)
    (hF : f.F={{c,h.e},{d,h.e}}) (r s : Coord) (hrs : r≠s)
    (hra : r≠a) (hrb : r≠b) (hre : r≠h.e) (hsa : s≠a) (hsb : s≠b) (hse : s≠h.e) :
    InPath p (triple a r s) := by
  apply (f.selected_iff r s hrs hra hrb hsa hsb).mpr
  rw [hF]; simp only [mem_insert,mem_singleton,not_or]
  exact ⟨Ne.symm (delta_pair_ne_right c h.e r s (Ne.symm hre) (Ne.symm hse)),
    Ne.symm (delta_pair_ne_right d h.e r s (Ne.symm hre) (Ne.symm hse))⟩

theorem ce_de_dx_cover (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.e},{d,h.e}}) :
    ∀w,InPath p w → Adj (triple a d h.x) w →
      w=pair d h.x ∨ w=quad a b d h.x ∨ w=quad a c d h.x ∨ w=quad a d h.e h.x := by
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a d h.x hadj
  by_cases hra : r=a
  · subst r; exact Or.inl (quad_cancel_first _ _ _)
  by_cases hrd : r=d
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.ordinary.absent_pair_a h.x hx.1 hx.2.1 hw)
  by_cases hrx : r=h.x
  · rw [hrx,quad_cancel_third] at hw
    exact False.elim (h.ordinary.absent_pair_a d (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd) hw)
  by_cases hrb : r=b
  · subst r; right; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrc : r=c
  · subst r; right; right; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hre : r=h.e
  · rw [hre]; right; right; right; exact quad_swap_last _ _ _ _
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have ht := h.ce_de_middle_without_e f hF h.x r (Ne.symm hrx) hx.1 hx.2.1 (Ne.symm h.hex) hra hrb hre
  have hp : InPath p (pair h.x r) := by
    apply (h.ordinary.left_pair_iff h.x r h.hx hr (Ne.symm hrx)).mpr
    rw [h.Aeq]; exact delta_pair_ne_right _ _ _ _ hre hrx
  have hq : InPath p (quad a b h.x r) := by
    apply (h.ordinary.right_pair_iff h.x r h.hx hr (Ne.symm hrx)).mpr
    rw [h.Beq]; exact delta_pair_ne _ _ _ _ (Ne.symm h.hex) h.hxy
  apply False.elim (two_layer_saturation p a b h.x r d h.ordinary.outer.hab
    (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd) hp hq ht _)
  have heq : quad a d h.x r=quad a h.x r d := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact heq ▸ hw

theorem ce_de_adex_selected (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.e},{d,h.e}}) :
    InPath p (quad a d h.e h.x) := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have htdx := h.ce_de_middle_without_e f hF d h.x (Ne.symm hx.2.2.2)
    (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd) (Ne.symm he.2.2.2)
    hx.1 hx.2.1 (Ne.symm h.hex)
  have htcx := h.ce_de_middle_without_e f hF c h.x (Ne.symm hx.2.2.1)
    (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) (Ne.symm he.2.2.1)
    hx.1 hx.2.1 (Ne.symm h.hex)
  have htcd := h.ce_de_middle_without_e f hF c d h.ordinary.outer.hcd
    (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) (Ne.symm he.2.2.1)
    (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd) (Ne.symm he.2.2.2)
  have hnrow : ¬AtMostOneNeighbor p (pair b h.x) := by
    apply h.core_internal f (h.ce_de_support f hF) _ (h.ordinary.row_selected h.x h.hx)
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_pair,Ne.symm hh.2.1,Ne.symm hkx]
  have hndx : ¬AtMostOneNeighbor p (triple a d h.x) := by
    apply h.core_internal f (h.ce_de_support f hF) _ htdx
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_triple,Ne.symm hh.1,Ne.symm hh.2.2.2,Ne.symm hkx]
  have hbdx := (force_two_neighbors p (pair b h.x) (triple b h.x c) (triple b h.x d)
    hnrow (h.ordinary.row_cover h.x h.hx)).2
  have hnbd : ¬InPath p (quad a b d h.x) := by
    have hn := ordinary_quad_absent p d a b h.x (Ne.symm h.ordinary.outer.had)
      (Ne.symm h.ordinary.outer.hab) hx.1 (Ne.symm hx.2.1)
      (by have heq : triple a b d=triple d a b := triple_rotate _ _ _
          exact heq ▸ h.ordinary.outer.habd_selected)
      (by have heq : triple a d h.x=triple d a h.x := by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
          exact heq ▸ htdx)
      (by simpa only [triple_rotate b h.x d] using hbdx)
    intro hs
    apply hn
    have heq : quad a b d h.x=quad d a b h.x := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact heq ▸ hs
  have hncd := ordinary_quad_absent p a c d h.x h.ordinary.outer.hac
    (Ne.symm h.ordinary.outer.hcd) hx.2.2.1 (Ne.symm hx.2.2.2) htcd htcx htdx
  apply (force_two_neighbors p (triple a d h.x) (pair d h.x) (quad a d h.e h.x) hndx ?_).2
  intro w hw hadj
  rcases h.ce_de_dx_cover f hF w hw hadj with hh | hh | hh | hh
  · exact Or.inl hh
  · exact False.elim (hnbd (hh ▸ hw))
  · exact False.elim (hncd (hh ▸ hw))
  · exact Or.inr hh

theorem ce_de_pair_cover (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.e},{d,h.e}}) :
    ∀w,InPath p w → Adj (pair d h.e) w →
      w=triple d h.e b ∨ w=triple d h.e c ∨ w=triple d h.e h.x := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hde := h.ordinary.side_pair h.e h.he
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair d h.e hadj
  by_cases hrd : r=d
  · subst r; rw [triple_cancel_left] at hw
    exact False.elim (h.ordinary.outer.absent_unit h.e he.1 he.2.2.1 hw)
  by_cases hre : r=h.e
  · rw [hre,triple_cancel_right] at hw
    exact False.elim (h.ordinary.outer.absent_unit d (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hcd) hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw
    have hm := (f.selected_iff d h.e (Ne.symm he.2.2.2) (Ne.symm h.ordinary.outer.had)
      (Ne.symm h.ordinary.outer.hbd) he.1 he.2.1).mp hw
    rw [hF] at hm; exact False.elim (hm (by simp))
  by_cases hrb : r=b
  · subst r; exact Or.inl rfl
  by_cases hrc : r=c
  · subst r; exact Or.inr (Or.inl rfl)
  by_cases hrx : r=h.x
  · rw [hrx]; exact Or.inr (Or.inr rfl)
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have hp : InPath p (pair h.e r) := by
    apply (h.ordinary.left_pair_iff h.e r h.he hr (Ne.symm hre)).mpr
    rw [h.Aeq]; exact delta_pair_ne_right _ _ _ _ hre hrx
  exact False.elim (selected_triple_forbidden p d h.e r (Ne.symm he.2.2.2) (Ne.symm hrd)
    (Ne.symm hre) hde (h.ordinary.side_pair r hr) hp hw)

theorem ce_de_cde_selected (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.e},{d,h.e}}) :
    InPath p (triple c d h.e) := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hde := h.ordinary.side_pair h.e h.he
  have hdx := h.ordinary.side_pair h.x h.hx
  have hq := h.ce_de_adex_selected f hF
  have hn : ¬InPath p (triple d h.e h.x) := by
    intro hs
    have hf := selected_flip_forbidden p (triple d h.e h.x) h.x h.e a
      (Ne.symm h.hex) hx.1 he.1 hs
      (by change InPath p (quad d h.e h.x h.x); simpa only [quad_cancel_third] using hde)
      (by change InPath p (quad d h.e h.x h.e); simpa only [quad_cancel_second] using hdx)
    apply hf
    change InPath p (quad d h.e h.x a)
    simpa only [quad_rotate d h.e h.x a] using hq
  have hnd : ¬AtMostOneNeighbor p (pair d h.e) := by
    apply h.core_internal f (h.ce_de_support f hF) _ hde
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_pair,Ne.symm hh.2.2.2,Ne.symm hke]
  have ht := (force_two_neighbors p (pair d h.e) (triple d h.e b) (triple d h.e c) hnd (by
    intro w hw hadj
    rcases h.ce_de_pair_cover f hF w hw hadj with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
    · exact False.elim (hn (hh ▸ hw)))).2
  simpa only [triple_rotate d h.e c] using ht

end SharedOuterConfig
#print axioms SharedOuterConfig.ce_de_adex_selected
#print axioms SharedOuterConfig.ce_de_cde_selected
end
end Snake9
