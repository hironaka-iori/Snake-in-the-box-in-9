import SharedOuterBase
import OrdinaryTwoEndpoints
import StarOuterResidual

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem right_hole_pair_selected : InPath p (pair h.e h.y) := by
  apply (h.ordinary.left_pair_iff h.e h.y h.he h.hy h.hey).mpr
  rw [h.Aeq,Finset.pair_comm h.e h.x]
  exact delta_pair_ne_right _ _ _ _ (Ne.symm h.hxy) (Ne.symm h.hey)

theorem right_hole_pair_cover (f : MissingAtNeighbor p a b) (hm : ({h.e,h.y}:Finset Coord)∈f.F) :
    ∀w,InPath p w → Adj (pair h.e h.y) w →
      w=triple h.e h.y c ∨ w=triple h.e h.y h.x := by
  have hx := (mem_distinctR a b c d h.e).mp h.he
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair h.e h.y hadj
  by_cases hrx : r=h.e
  · rw [hrx,triple_cancel_left] at hw
    exact False.elim (h.ordinary.outer.absent_unit h.y hy.1 hy.2.2.1 hw)
  by_cases hry : r=h.y
  · rw [hry,triple_cancel_right] at hw
    exact False.elim (h.ordinary.outer.absent_unit h.e hx.1 hx.2.2.1 hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw
    exact False.elim ((f.selected_iff h.e h.y h.hey hx.1 hx.2.1 hy.1 hy.2.1).mp hw hm)
  by_cases hrb : r=b
  · subst r; rw [triple_rotate] at hw
    exact False.elim (h.ordinary.ordinary_b_absent h.e h.y h.he h.hy h.hey hw)
  by_cases hrc : r=c
  · subst r; exact Or.inl rfl
  by_cases hre : r=h.x
  · rw [hre]; exact Or.inr rfl
  by_cases hrd : r=d
  · subst r
    exact False.elim (selected_triple_forbidden p h.e h.y d h.hey hx.2.2.2 hy.2.2.2 h.right_hole_pair_selected
      (by simpa only [pair_comm d h.e] using h.ordinary.side_pair h.e h.he)
      (by simpa only [pair_comm d h.y] using h.ordinary.side_pair h.y h.hy) hw)
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have hxr : InPath p (pair h.e r) := by
    apply (h.ordinary.left_pair_iff h.e r h.he hr (Ne.symm hrx)).mpr
    rw [h.Aeq,Finset.pair_comm h.e h.x]; exact delta_pair_ne_right _ _ _ _ hre hrx
  have hyr : InPath p (pair h.y r) := by
    apply (h.ordinary.left_pair_iff h.y r h.hy hr (Ne.symm hry)).mpr
    rw [h.Aeq,Finset.pair_comm h.e h.x]; exact delta_pair_ne _ _ _ _ (Ne.symm h.hxy) (Ne.symm h.hey)
  exact False.elim (selected_triple_forbidden p h.e h.y r h.hey (Ne.symm hrx) (Ne.symm hry)
    h.right_hole_pair_selected hxr hyr hw)

theorem missing_right_c_cover (f : MissingAtNeighbor p a b) (hcy : ({c,h.y}:Finset Coord)∉f.F) (hdy : ({d,h.y}:Finset Coord)∉f.F)
    (hcd : ({c,d}:Finset Coord)∉f.F)
    (haway : ∀r∈distinctR a b c d,r≠h.y → r≠h.e → ({h.y,r}:Finset Coord)∉f.F)
    (hnc : ¬InPath p (pair c h.y)) :
    ∀w, InPath p w → Adj (triple a c h.y) w →
      w=quad a b c h.y ∨ w=quad a c h.e h.y := by
  obtain ⟨hya,hyb,hyc,hyd⟩ := (mem_distinctR a b c d h.y).mp h.hy
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a c h.y hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw; exact False.elim (hnc hw)
  by_cases hrc : r=c
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.ordinary.absent_pair_a h.y hya hyb hw)
  by_cases hry : r=h.y
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.ordinary.absent_pair_a c (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hre : r=h.e
  · subst r; right; exact quad_swap_last _ _ _ _
  by_cases hrd : r=d
  · subst r
    have hce := (mem_distinctR a b c d h.y).mp h.hy
    have htc := (f.selected_iff c h.y (Ne.symm hce.2.2.1) (Ne.symm h.ordinary.outer.hac)
      (Ne.symm h.ordinary.outer.hbc) hce.1 hce.2.1).mpr hcy
    have htd := (f.selected_iff d h.y (Ne.symm hce.2.2.2) (Ne.symm h.ordinary.outer.had)
      (Ne.symm h.ordinary.outer.hbd) hce.1 hce.2.1).mpr hdy
    have htcd := (f.selected_iff c d h.ordinary.outer.hcd (Ne.symm h.ordinary.outer.hac)
      (Ne.symm h.ordinary.outer.hbc) (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd)).mpr hcd
    have habs := ordinary_quad_absent p a c d h.y h.ordinary.outer.hac
      (Ne.symm h.ordinary.outer.hcd) hce.2.2.1 (Ne.symm hce.2.2.2) htcd htc htd
    exact False.elim (habs (by simpa only [quad_swap_last a c h.y d] using hw))
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have hnA : ({h.y,r}:Finset Coord)≠h.ordinary.A := by
    rw [h.Aeq]
    exact delta_pair_ne _ _ _ _ (Ne.symm h.hey) (Ne.symm h.hxy)
  have hnB : ({h.y,r}:Finset Coord)≠h.ordinary.B := by
    rw [h.Beq]
    exact delta_pair_ne_right _ _ _ _ hre hry
  have hm := (f.selected_iff h.y r (Ne.symm hry) hya hyb hra hrb).mpr (haway r hr hry hre)
  have habs := two_layer_saturation p a b h.y r c h.ordinary.outer.hab
    (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc)
    ((h.ordinary.left_pair_iff h.y r h.hy hr (Ne.symm hry)).mpr hnA)
    ((h.ordinary.right_pair_iff h.y r h.hy hr (Ne.symm hry)).mpr hnB) hm
  have heq : quad a c h.y r=quad a h.y r c := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact False.elim (habs (heq ▸ hw))

theorem missing_right_core_false (f : MissingAtNeighbor p a b)
    (hm : ({h.e,h.y}:Finset Coord)∈f.F)
    (hce : ({c,h.e}:Finset Coord)∉f.F) (hcd : ({c,d}:Finset Coord)∉f.F)
    (hcy : ({c,h.y}:Finset Coord)∉f.F) (hdy : ({d,h.y}:Finset Coord)∉f.F)
    (haway : ∀r∈distinctR a b c d,r≠h.y → r≠h.e → ({h.y,r}:Finset Coord)∉f.F)
    (hnb : ¬AtMostOneNeighbor p (pair b h.y))
    (hnc : ¬AtMostOneNeighbor p (triple a c h.y))
    (hne : ¬AtMostOneNeighbor p (pair h.e h.y)) : False := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d h.y).mp h.hy
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hacy := (f.selected_iff c h.y (Ne.symm hkc) (Ne.symm h.ordinary.outer.hac)
    (Ne.symm h.ordinary.outer.hbc) hka hkb).mpr hcy
  have hace := (f.selected_iff c h.e (Ne.symm he.2.2.1) (Ne.symm h.ordinary.outer.hac)
    (Ne.symm h.ordinary.outer.hbc) he.1 he.2.1).mpr hce
  have hr := force_two_neighbors p (pair b h.y) (triple b h.y c) (triple b h.y d)
    hnb (h.ordinary.row_cover h.y h.hy)
  have hnck : ¬InPath p (pair c h.y) := by
    intro hck
    have adj1 : Adj (pair c h.y) (unit c) := adj_symmetric (unit_pair_adj _ _)
    have adj2 : Adj (pair c h.y) (triple a c h.y) := by
      have he : triple a c h.y=triple c h.y a := by
        apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
      rw [he]; exact pair_triple_adj _ _ _
    have adj3 : Adj (pair c h.y) (triple b h.y c) := by
      have he : triple b h.y c=triple c h.y b := by
        apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
      rw [he]; exact pair_triple_adj _ _ _
    rcases selected_three_neighbors_repeat p hck h.ordinary.outer.hc hacy hr.1 adj1 adj2 adj3 with he | he | he
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_unit,bit_triple,Ne.symm h.ordinary.outer.hac,hka] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
      simp [bit_unit,bit_triple,Ne.symm h.ordinary.outer.hbc,hkb] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.ordinary.outer.hab,Ne.symm h.ordinary.outer.hac,hka] at hb
  have hq := (force_two_neighbors p (triple a c h.y) (quad a b c h.y) (quad a c h.e h.y)
    hnc (h.missing_right_c_cover f hcy hdy hcd haway hnck)).2
  have hside := (force_two_neighbors p (pair h.e h.y) (triple h.e h.y c) (triple h.e h.y h.x)
    hne (h.right_hole_pair_cover f hm)).1
  have habs := quad_two_rows_excludes_side p a c h.e h.y h.ordinary.outer.hac
    (Ne.symm he.1) (Ne.symm hka) h.hey hq hace hacy
  exact habs (by simpa only [triple_rotate h.e h.y c] using hside)

theorem missing_right_two_rows_false (f : MissingAtNeighbor p a b)
    (hm : ({h.e,h.y}:Finset Coord)∈f.F)
    (hce : ({c,h.e}:Finset Coord)∉f.F) (hcd : ({c,d}:Finset Coord)∉f.F)
    (hcy : ({c,h.y}:Finset Coord)∉f.F) (hdy : ({d,h.y}:Finset Coord)∉f.F)
    (haway : ∀r∈distinctR a b c d,r≠h.y → r≠h.e → ({h.y,r}:Finset Coord)∉f.F)
    (u v : Coord) (hu : u∈distinctR a b c d) (hv : v∈distinctR a b c d) (huv : u≠v)
    (hue : u≠h.e) (huy : u≠h.y) (hve : v≠h.e) (hvy : v≠h.y)
    (hU : OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d u)
    (hV : OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d v) : False := by
  have hhu := (mem_distinctR a b c d u).mp hu
  have hhv := (mem_distinctR a b c d v).mp hv
  have hhy := (mem_distinctR a b c d h.y).mp h.hy
  have nonlow := h.ordinary.nonlow_outside_two f u v hu hv huv hU hV
  apply h.missing_right_core_false f hm hce hcd hcy hdy haway
  · apply nonlow _ (h.ordinary.row_selected h.y h.hy)
    · simp [bit_pair,Ne.symm hhu.2.1,Ne.symm huy]
    · simp [bit_pair,Ne.symm hhv.2.1,Ne.symm hvy]
  · have hs := (f.selected_iff c h.y (Ne.symm hhy.2.2.1) (Ne.symm h.ordinary.outer.hac)
      (Ne.symm h.ordinary.outer.hbc) hhy.1 hhy.2.1).mpr hcy
    apply nonlow _ hs
    · simp [bit_triple,Ne.symm hhu.1,Ne.symm hhu.2.2.1,Ne.symm huy]
    · simp [bit_triple,Ne.symm hhv.1,Ne.symm hhv.2.2.1,Ne.symm hvy]
  · apply nonlow _ h.right_hole_pair_selected
    · simp [bit_pair,Ne.symm hue,Ne.symm huy]
    · simp [bit_pair,Ne.symm hve,Ne.symm hvy]

end SharedOuterConfig
#print axioms SharedOuterConfig.right_hole_pair_cover
#print axioms SharedOuterConfig.missing_right_c_cover
#print axioms SharedOuterConfig.missing_right_core_false
#print axioms SharedOuterConfig.missing_right_two_rows_false
end
end Snake9
