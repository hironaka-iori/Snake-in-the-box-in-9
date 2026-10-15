import SharedOuterSwitch
import SharedCleanRows

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem switch_family_false (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y)
    (hF : f.F={{h.e,k},{h.x,h.y}}) : False := by
  obtain ⟨u,v,huv,hu,hue,hux,huy,hv,hve,hvx,hvy⟩ := h.two_clean_indices
  by_cases huk : u=k
  · exact h.switch_impossible f k v hk hv hke hkx hky hve hvx hvy
      (by intro hvk; exact huv (huk.trans hvk.symm)) hF
  · exact h.switch_impossible f k u hk hu hke hkx hky hue hux huy huk hF

end SharedOuterConfig
#print axioms SharedOuterConfig.switch_family_false
end
end Snake9
