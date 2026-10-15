import SharedOuterSwitch
import SharedCleanRows
import OrdinaryPartialRows
import OrdinaryGoodRowMirror

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2500000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem cross_c_cover (f : MissingAtNeighbor p a b)
    (hcstar : ∀r∈distinctR a b c d,({c,r}:Finset Coord)∉f.F)
    (hcd : ({c,d}:Finset Coord)∉f.F) (hdx : ({d,h.x}:Finset Coord)∉f.F)
    (hspokes : ∀r∈distinctR a b c d,r≠h.x → r≠h.y → ({h.x,r}:Finset Coord)∉f.F)
    (hnc : ¬InPath p (pair c h.x)) :
    ∀w,InPath p w → Adj (triple a c h.x) w →
      w=quad a b c h.x ∨ w=quad a c h.x h.y := by
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have htcd := (f.selected_iff c d h.ordinary.outer.hcd (Ne.symm h.ordinary.outer.hac)
    (Ne.symm h.ordinary.outer.hbc) (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd)).mpr hcd
  have htcx := (f.selected_iff c h.x (Ne.symm hx.2.2.1) (Ne.symm h.ordinary.outer.hac)
    (Ne.symm h.ordinary.outer.hbc) hx.1 hx.2.1).mpr (hcstar h.x h.hx)
  have htdx := (f.selected_iff d h.x (Ne.symm hx.2.2.2) (Ne.symm h.ordinary.outer.had)
    (Ne.symm h.ordinary.outer.hbd) hx.1 hx.2.1).mpr hdx
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a c h.x hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw; exact False.elim (hnc hw)
  by_cases hrc : r=c
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.ordinary.absent_pair_a h.x hx.1 hx.2.1 hw)
  by_cases hrx : r=h.x
  · rw [hrx,quad_cancel_third] at hw
    exact False.elim (h.ordinary.absent_pair_a c (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hry : r=h.y
  · rw [hry]; exact Or.inr rfl
  by_cases hrd : r=d
  · subst r
    have hn := ordinary_quad_absent p a c d h.x h.ordinary.outer.hac
      (Ne.symm h.ordinary.outer.hcd) hx.2.2.1 (Ne.symm hx.2.2.2) htcd htcx htdx
    exact False.elim (hn (by simpa only [quad_swap_last a c h.x d] using hw))
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have hn := h.ordinary.partial_side_saturation f h.x r c h.hx hr (Ne.symm hrx)
    (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) (Ne.symm hx.2.2.1)
    (Ne.symm hrc) (hcstar h.x h.hx) (hspokes r hr hrx hry) (fun _ => hcstar r hr)
  apply False.elim (hn _)
  have heq : quad a c h.x r=quad a h.x r c := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact heq ▸ hw

theorem cross_c_core_false (f : MissingAtNeighbor p a b)
    (hm : ({h.x,h.y}:Finset Coord)∈f.F)
    (hcstar : ∀r∈distinctR a b c d,({c,r}:Finset Coord)∉f.F)
    (hcd : ({c,d}:Finset Coord)∉f.F) (hdx : ({d,h.x}:Finset Coord)∉f.F)
    (hspokes : ∀r∈distinctR a b c d,r≠h.x → r≠h.y → ({h.x,r}:Finset Coord)∉f.F)
    (hnb : ¬AtMostOneNeighbor p (pair b h.x))
    (hnc : ¬AtMostOneNeighbor p (triple a c h.x))
    (hnxy : ¬AtMostOneNeighbor p (pair h.x h.y)) : False := by
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have htcx := (f.selected_iff c h.x (Ne.symm hx.2.2.1) (Ne.symm h.ordinary.outer.hac)
    (Ne.symm h.ordinary.outer.hbc) hx.1 hx.2.1).mpr (hcstar h.x h.hx)
  have htcy := (f.selected_iff c h.y (Ne.symm hy.2.2.1) (Ne.symm h.ordinary.outer.hac)
    (Ne.symm h.ordinary.outer.hbc) hy.1 hy.2.1).mpr (hcstar h.y h.hy)
  have hbcx := (force_two_neighbors p (pair b h.x) (triple b h.x c) (triple b h.x d)
    hnb (h.ordinary.row_cover h.x h.hx)).1
  have hncx : ¬InPath p (pair c h.x) := by
    intro hs
    have adj1 : Adj (pair c h.x) (unit c) := adj_symmetric (unit_pair_adj _ _)
    have adj2 : Adj (pair c h.x) (triple a c h.x) := by
      rw [←triple_rotate c h.x a]; exact pair_triple_adj _ _ _
    have adj3 : Adj (pair c h.x) (triple b h.x c) := by
      have heq : triple b h.x c=triple c h.x b := by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
      rw [heq]; exact pair_triple_adj _ _ _
    rcases selected_three_neighbors_repeat p hs h.ordinary.outer.hc htcx hbcx adj1 adj2 adj3 with he | he | he
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_unit,bit_triple,Ne.symm h.ordinary.outer.hac,hx.1] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
      simp [bit_unit,bit_triple,Ne.symm h.ordinary.outer.hbc,hx.2.1] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.ordinary.outer.hab,Ne.symm h.ordinary.outer.hac,hx.1] at hb
  have hq := (force_two_neighbors p (triple a c h.x) (quad a b c h.x) (quad a c h.x h.y)
    hnc (h.cross_c_cover f hcstar hcd hdx hspokes hncx)).2
  have hside := (force_two_neighbors p (pair h.x h.y) (triple h.x h.y c) (triple h.x h.y h.e)
    hnxy (h.cross_pair_cover f hm)).1
  have hn := quad_two_rows_excludes_side p a c h.x h.y h.ordinary.outer.hac
    (Ne.symm hx.1) (Ne.symm hy.1) h.hxy hq htcx htcy
  exact hn (by simpa only [triple_rotate h.x h.y c] using hside)

theorem cross_c_two_rows_false (f : MissingAtNeighbor p a b)
    (hm : ({h.x,h.y}:Finset Coord)∈f.F)
    (hcstar : ∀r∈distinctR a b c d,({c,r}:Finset Coord)∉f.F)
    (hcd : ({c,d}:Finset Coord)∉f.F) (hdx : ({d,h.x}:Finset Coord)∉f.F)
    (hspokes : ∀r∈distinctR a b c d,r≠h.x → r≠h.y → ({h.x,r}:Finset Coord)∉f.F)
    (u v : Coord) (hu : u∈distinctR a b c d) (hv : v∈distinctR a b c d) (huv : u≠v)
    (hux : u≠h.x) (huy : u≠h.y) (hvx : v≠h.x) (hvy : v≠h.y)
    (hU : OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d u)
    (hV : OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d v) : False := by
  have hhu := (mem_distinctR a b c d u).mp hu
  have hhv := (mem_distinctR a b c d v).mp hv
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have nonlow := h.ordinary.nonlow_outside_two f u v hu hv huv hU hV
  apply h.cross_c_core_false f hm hcstar hcd hdx hspokes
  · apply nonlow _ (h.ordinary.row_selected h.x h.hx)
    · simp [bit_pair,Ne.symm hhu.2.1,Ne.symm hux]
    · simp [bit_pair,Ne.symm hhv.2.1,Ne.symm hvx]
  · apply nonlow _ ((f.selected_iff c h.x (Ne.symm hx.2.2.1) (Ne.symm h.ordinary.outer.hac)
      (Ne.symm h.ordinary.outer.hbc) hx.1 hx.2.1).mpr (hcstar h.x h.hx))
    · simp [bit_triple,Ne.symm hhu.1,Ne.symm hhu.2.2.1,Ne.symm hux]
    · simp [bit_triple,Ne.symm hhv.1,Ne.symm hhv.2.2.1,Ne.symm hvx]
  · apply nonlow _ h.cross_pair_selected
    · simp [bit_pair,Ne.symm hux,Ne.symm huy]
    · simp [bit_pair,Ne.symm hvx,Ne.symm hvy]

end SharedOuterConfig
#print axioms SharedOuterConfig.cross_c_core_false
#print axioms SharedOuterConfig.cross_c_two_rows_false
end
end Snake9
