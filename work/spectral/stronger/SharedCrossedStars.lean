import SharedCrossStars
import OrdinaryMissingStarCover

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem crossed_d_pair_cover (f : MissingAtNeighbor p a b) (hm : ({d,h.x}:Finset Coord)∈f.F)
    (hade : InPath p (triple a d h.e)) (hnbe : ¬AtMostOneNeighbor p (pair b h.e)) :
    ∀w, InPath p w → Adj (pair d h.x) w → w=triple b d h.x ∨ w=triple c d h.x := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d h.x).mp h.hx
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hbde := (force_two_neighbors p (pair b h.e) (triple b h.e c) (triple b h.e d)
    hnbe (h.ordinary.row_cover h.e h.he)).2
  have hbad : ¬InPath p (triple d h.x h.e) := by
    have haSel : InPath p (SquareIncidence.flip a (pair d h.e)) := by
      change InPath p (triple d h.e a)
      rw [triple_rotate]
      exact hade
    have hbSel : InPath p (SquareIncidence.flip b (pair d h.e)) := by
      change InPath p (triple d h.e b)
      rw [triple_rotate]
      simpa only [triple_swap b h.e d] using hbde
    have hn := selected_flip_forbidden p (pair d h.e) a b h.x h.ordinary.outer.hab
      (Ne.symm hka) (Ne.symm hkb) (h.ordinary.side_pair h.e h.he) haSel hbSel
    intro hs
    apply hn
    change InPath p (triple d h.e h.x)
    simpa only [triple_swap d h.x h.e] using hs
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair d h.x hadj
  by_cases hrd : r=d
  · subst r; rw [triple_cancel_left] at hw
    exact False.elim (h.ordinary.outer.absent_unit h.x hka hkc hw)
  by_cases hrk : r=h.x
  · subst r; rw [triple_cancel_right] at hw
    exact False.elim (h.ordinary.outer.absent_unit d (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hcd) hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw
    exact False.elim ((f.selected_iff d h.x (Ne.symm hkd) (Ne.symm h.ordinary.outer.had)
      (Ne.symm h.ordinary.outer.hbd) hka hkb).mp hw hm)
  by_cases hrb : r=b
  · subst r; left; exact triple_rotate _ _ _
  by_cases hrc : r=c
  · subst r; right; exact triple_rotate _ _ _
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  by_cases hre : r=h.e
  · exact False.elim (hbad (by simpa only [hre] using hw))
  have hxr : InPath p (pair h.x r) := by
    apply (h.ordinary.left_pair_iff h.x r h.hx hr (Ne.symm hrk)).mpr
    rw [h.Aeq]
    exact delta_pair_ne_right _ _ _ _ hre hrk
  exact False.elim (selected_triple_forbidden p d h.x r (Ne.symm hkd) (Ne.symm hrd)
    (Ne.symm hrk) (h.ordinary.side_pair h.x h.hx) (h.ordinary.side_pair r hr) hxr hw)

theorem cy_dx_false (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.y},{d,h.x}}) : False := by
  have hx := (mem_distinctR a b c d h.y).mp h.hy
  have hy := (mem_distinctR a b c d h.x).mp h.hx
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hsupp : ∀s∈f.F,s⊆{c,d,h.e,h.x,h.y} := by
    intro s hs
    rw [hF] at hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · rw [Finset.mem_singleton.mp hs]
      simp [Finset.insert_subset_iff,Finset.singleton_subset_iff]

  have hck : ({c,h.x}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ hy.2.2.1 (Ne.symm (Ne.symm h.hxy)),
      delta_pair_ne _ _ _ _ h.ordinary.outer.hcd (Ne.symm hy.2.2.1)⟩
  have hdk : ({d,h.x}:Finset Coord)∈f.F := by rw [hF]; simp
  have hcd : ({c,d}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ (Ne.symm h.ordinary.outer.hcd) (Ne.symm hx.2.2.2),
      delta_pair_ne _ _ _ _ h.ordinary.outer.hcd (Ne.symm hy.2.2.1)⟩
  have hce : ({c,h.e}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ he.2.2.1 h.hey,
      delta_pair_ne _ _ _ _ h.ordinary.outer.hcd (Ne.symm hy.2.2.1)⟩
  have hspokes : ∀r∈distinctR a b c d,r≠h.x → ({h.x,r}:Finset Coord)∉f.F := by
    intro r hr hry
    have hh := (mem_distinctR a b c d r).mp hr
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ hy.2.2.1 (Ne.symm (Ne.symm h.hxy)),
      delta_pair_ne_right _ _ _ _ hh.2.2.2 hry⟩
  have hpartner : ∀r∈distinctR a b c d,
      (({h.x,r}:Finset Coord)=h.ordinary.A ∨ ({h.x,r}:Finset Coord)=h.ordinary.B) → ({c,r}:Finset Coord)∉f.F := by
    intro r hr hh
    rcases hh with hh | hh
    · rw [h.Aeq] at hh
      have hr' : r=h.e := by
        have hm : h.e∈({h.x,r}:Finset Coord) := hh.symm ▸ (by simp)
        simpa [h.hex,eq_comm] using hm
      simpa only [hr'] using hce
    · have hxB : h.x∉h.ordinary.B := by simp [h.Beq,Ne.symm h.hex,h.hxy]
      exact False.elim (hxB (hh ▸ (by simp : h.x∈({h.x,r}:Finset Coord))))
  have htc := (f.selected_iff c h.x (Ne.symm hy.2.2.1) (Ne.symm h.ordinary.outer.hac)
    (Ne.symm h.ordinary.outer.hbc) hy.1 hy.2.1).mpr hck
  have hde : ({d,h.e}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm h.ordinary.outer.hcd) (Ne.symm hx.2.2.2),
      delta_pair_ne_right _ _ _ _ he.2.2.2 h.hex⟩
  have hade := (f.selected_iff d h.e (Ne.symm he.2.2.2) (Ne.symm h.ordinary.outer.had)
    (Ne.symm h.ordinary.outer.hbd) he.1 he.2.1).mpr hde
  have hnbe : ¬AtMostOneNeighbor p (pair b h.e) := by
    apply h.core_internal f hsupp _ (h.ordinary.row_selected h.e h.he)
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_pair,Ne.symm hh.2.1,Ne.symm hke]
  have hcover := h.crossed_d_pair_cover f hdk hade hnbe
  rcases h.ordinary.missing_d_row_endpoint_of_cover f h.x h.hx hck hcd hspokes hpartner hcover with hl | hl | hl
  · apply h.core_internal f hsupp _ (h.ordinary.row_selected h.x h.hx) _ hl
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_pair,Ne.symm hh.2.1,Ne.symm hkx]
  · apply h.core_internal f hsupp _ htc _ hl
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_triple,Ne.symm hh.1,Ne.symm hh.2.2.1,Ne.symm hkx]
  · apply h.core_internal f hsupp _ (h.ordinary.side_pair h.x h.hx) _ hl
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_pair,Ne.symm hh.2.2.2,Ne.symm hkx]

end SharedOuterConfig
#print axioms SharedOuterConfig.crossed_d_pair_cover
#print axioms SharedOuterConfig.cy_dx_false
end
end Snake9
