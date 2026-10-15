import SharedMissingRight
import SharedCleanRows

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem missing_right_family_impossible (f : MissingAtNeighbor p a b) (S : Finset Coord)
    (hF : f.F={{h.e,h.y},S}) (hS : S⊆{c,d,h.e,h.x})
    (hncd : S≠{c,d}) (hnce : S≠{c,h.e}) : False := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have hyS : h.y∉S := by
    intro hh
    have hs := hS hh
    simpa [hy.2.2.1,hy.2.2.2,Ne.symm h.hey,Ne.symm h.hxy] using hs
  have hyPair (r : Coord) : ({h.y,r}:Finset Coord)≠S := by
    intro hh
    exact hyS (hh ▸ (by simp : h.y∈({h.y,r}:Finset Coord)))
  have hm : ({h.e,h.y}:Finset Coord)∈f.F := by rw [hF]; simp
  have hce : ({c,h.e}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm he.2.2.1) (Ne.symm hy.2.2.1),Ne.symm hnce⟩
  have hcd : ({c,d}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm he.2.2.1) (Ne.symm hy.2.2.1),Ne.symm hncd⟩
  have hcy : ({c,h.y}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    refine ⟨delta_pair_ne _ _ _ _ (Ne.symm he.2.2.1) (Ne.symm hy.2.2.1),?_⟩
    simpa only [Finset.pair_comm c h.y] using hyPair c
  have hdy : ({d,h.y}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    refine ⟨delta_pair_ne _ _ _ _ (Ne.symm he.2.2.2) (Ne.symm hy.2.2.2),?_⟩
    simpa only [Finset.pair_comm d h.y] using hyPair d
  have haway : ∀r∈distinctR a b c d,r≠h.y → r≠h.e → ({h.y,r}:Finset Coord)∉f.F := by
    intro r hr hry hre
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ hre hry,hyPair r⟩
  obtain ⟨u,v,huv,hu,hue,hux,huy,hv,hve,hvx,hvy⟩ := h.two_clean_indices
  have his (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y) :
      ∀t∈f.F,k∉t := by
    intro t ht hkt
    rw [hF] at ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · simpa [hke,hky] using hkt
    · have hh := (mem_distinctR a b c d k).mp hk
      have hs := hS ((Finset.mem_singleton.mp ht) ▸ hkt)
      simpa [hh.2.2.1,hh.2.2.2,hke,hkx] using hs
  exact h.missing_right_two_rows_false f hm hce hcd hcy hdy haway u v hu hv huv hue huy hve hvy
    (h.clean_isolated_good f u hu hue hux huy (his u hu hue hux huy))
    (h.clean_isolated_good f v hv hve hvx hvy (his v hv hve hvx hvy))

end SharedOuterConfig
#print axioms SharedOuterConfig.missing_right_family_impossible
end
end Snake9
