import SharedCrossMissingStar

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2000000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem B_xy_false (f : MissingAtNeighbor p a b)
    (hF : f.F={{h.e,h.y},{h.x,h.y}}) : False := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have hcstar (s : Coord) (hs : s∈distinctR a b c d) : ({c,s}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm he.2.2.1) (Ne.symm hy.2.2.1),
      delta_pair_ne _ _ _ _ (Ne.symm hx.2.2.1) (Ne.symm hy.2.2.1)⟩
  have hcd : ({c,d}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm he.2.2.1) (Ne.symm hy.2.2.1),
      delta_pair_ne _ _ _ _ (Ne.symm hx.2.2.1) (Ne.symm hy.2.2.1)⟩
  have hdx : ({d,h.x}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm he.2.2.2) (Ne.symm hy.2.2.2),
      delta_pair_ne _ _ _ _ (Ne.symm hx.2.2.2) (Ne.symm hy.2.2.2)⟩
  have hspokes (s : Coord) (hs : s∈distinctR a b c d) (hsx : s≠h.x) (hsy : s≠h.y) :
      ({h.x,s}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm h.hex) h.hxy,
      delta_pair_ne_right _ _ _ _ hsx hsy⟩
  obtain ⟨u,v,huv,hu,hue,hux,huy,hv,hve,hvx,hvy⟩ := h.two_clean_indices
  have good (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y) :
      OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d k := by
    apply h.clean_isolated_good f k hk hke hkx hky
    rw [hF]
    intro s hs
    simp only [mem_insert,mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp [hke,hkx,hky]
  exact h.cross_c_two_rows_false f (by rw [hF]; simp) hcstar hcd hdx hspokes
    u v hu hv huv hux huy hvx hvy (good u hu hue hux huy) (good v hv hve hvx hvy)

theorem A_xy_false (f : MissingAtNeighbor p a b)
    (hF : f.F={{h.e,h.x},{h.x,h.y}}) : False := by
  apply h.mirror.B_xy_false f.mirror
  change f.F={{h.e,h.x},{h.y,h.x}}
  simpa only [Finset.pair_comm h.y h.x] using hF

end SharedOuterConfig
#print axioms SharedOuterConfig.B_xy_false
#print axioms SharedOuterConfig.A_xy_false
end
end Snake9
