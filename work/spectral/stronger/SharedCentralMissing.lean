import SharedCentralGeometry

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem cd_ce_middle_without_c (f : MissingAtNeighbor p a b)
    (hF : f.F={{c,d},{c,h.e}}) (r s : Coord) (hrs : r≠s)
    (hra : r≠a) (hrb : r≠b) (hrc : r≠c) (hsa : s≠a) (hsb : s≠b) (hsc : s≠c) :
    InPath p (triple a r s) := by
  apply (f.selected_iff r s hrs hra hrb hsa hsb).mpr
  rw [hF]; simp only [mem_insert,mem_singleton,not_or]
  exact ⟨Ne.symm (delta_pair_ne c d r s (Ne.symm hrc) (Ne.symm hsc)),
    Ne.symm (delta_pair_ne c h.e r s (Ne.symm hrc) (Ne.symm hsc))⟩

theorem cd_ce_left_cover (f : MissingAtNeighbor p a b) (hF : f.F={{c,d},{c,h.e}}) :
    ∀w,InPath p w → Adj (triple a h.e h.x) w →
      w=quad a b h.e h.x ∨ w=quad a c h.e h.x := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have ht := h.cd_ce_middle_without_c f hF h.e h.x h.hex he.1 he.2.1 he.2.2.1 hx.1 hx.2.1 hx.2.2.1
  have hde := h.cd_ce_middle_without_c f hF d h.e (Ne.symm he.2.2.2) (Ne.symm h.ordinary.outer.had)
    (Ne.symm h.ordinary.outer.hbd) (Ne.symm h.ordinary.outer.hcd) he.1 he.2.1 he.2.2.1
  have hdx := h.cd_ce_middle_without_c f hF d h.x (Ne.symm hx.2.2.2) (Ne.symm h.ordinary.outer.had)
    (Ne.symm h.ordinary.outer.hbd) (Ne.symm h.ordinary.outer.hcd) hx.1 hx.2.1 hx.2.2.1
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a h.e h.x hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw
    exact False.elim ((h.ordinary.left_pair_iff h.e h.x h.he h.hx h.hex).mp hw h.Aeq.symm)
  by_cases hre : r=h.e
  · rw [hre,quad_cancel_second] at hw
    exact False.elim (h.ordinary.absent_pair_a h.x hx.1 hx.2.1 hw)
  by_cases hrx : r=h.x
  · rw [hrx,quad_cancel_third] at hw
    exact False.elim (h.ordinary.absent_pair_a h.e he.1 he.2.1 hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrc : r=c
  · subst r; right; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrd : r=d
  · subst r
    exact False.elim (ordinary_quad_absent p a h.e h.x d (Ne.symm he.1) (Ne.symm h.hex)
      (Ne.symm he.2.2.2) hx.2.2.2 ht
      (by simpa only [triple_swap a d h.e] using hde)
      (by simpa only [triple_swap a d h.x] using hdx) hw)
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have hm := (h.ordinary.left_hole_extension f h.e h.x r h.hex h.Aeq.symm hr hre hrx hw).2
  rcases hm with hm | hb
  · rw [hF] at hm
    rcases Finset.mem_insert.mp hm with heq | heq
    · exact False.elim (delta_pair_ne c d h.x r (Ne.symm hx.2.2.1) (Ne.symm hrc) heq.symm)
    · exact False.elim (delta_pair_ne c h.e h.x r (Ne.symm hx.2.2.1) (Ne.symm hrc) (Finset.mem_singleton.mp heq).symm)
  · rw [h.Beq] at hb
    exact False.elim (delta_pair_ne h.x r h.e h.y (Ne.symm h.hex) h.hxy hb)

theorem cd_ce_dx_cover (f : MissingAtNeighbor p a b) (hF : f.F={{c,d},{c,h.e}}) :
    ∀w,InPath p w → Adj (triple a d h.x) w →
      w=pair d h.x ∨ w=quad a b d h.x ∨ w=quad a c d h.x ∨ w=quad a d h.e h.x := by
  have he := (mem_distinctR a b c d h.e).mp h.he
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
  have ht := h.cd_ce_middle_without_c f hF h.x r (Ne.symm hrx) hx.1 hx.2.1 hx.2.2.1 hra hrb hrc
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

theorem cd_ce_impossible (f : MissingAtNeighbor p a b) (hF : f.F={{c,d},{c,h.e}})
    (hnrow : ¬AtMostOneNeighbor p (pair b h.x))
    (hnex : ¬AtMostOneNeighbor p (triple a h.e h.x))
    (hndx : ¬AtMostOneNeighbor p (triple a d h.x)) : False := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have htex := h.cd_ce_middle_without_c f hF h.e h.x h.hex he.1 he.2.1 he.2.2.1 hx.1 hx.2.1 hx.2.2.1
  have htdx := h.cd_ce_middle_without_c f hF d h.x (Ne.symm hx.2.2.2) (Ne.symm h.ordinary.outer.had)
    (Ne.symm h.ordinary.outer.hbd) (Ne.symm h.ordinary.outer.hcd) hx.1 hx.2.1 hx.2.2.1
  have htcx : InPath p (triple a c h.x) := by
    apply (f.selected_iff c h.x (Ne.symm hx.2.2.1) (Ne.symm h.ordinary.outer.hac)
      (Ne.symm h.ordinary.outer.hbc) hx.1 hx.2.1).mpr
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ hx.2.2.1 hx.2.2.2,
      delta_pair_ne_right _ _ _ _ hx.2.2.1 (Ne.symm h.hex)⟩
  exact h.central_ladder_impossible htex htcx htdx hnrow hnex hndx
    (h.cd_ce_left_cover f hF) (h.cd_ce_dx_cover f hF)

end SharedOuterConfig
#print axioms SharedOuterConfig.cd_ce_impossible
end
end Snake9
