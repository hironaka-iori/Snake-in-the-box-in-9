import SharedCentralMissing
import SharedCleanRows
import OrdinaryGoodRowMirror

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem cd_ce_two_rows_false (f : MissingAtNeighbor p a b) (hF : f.F={{c,d},{c,h.e}})
    (u v : Coord) (hu : u∈distinctR a b c d) (hv : v∈distinctR a b c d) (huv : u≠v)
    (hue : u≠h.e) (hux : u≠h.x) (hve : v≠h.e) (hvx : v≠h.x)
    (hU : OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d u)
    (hV : OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d v) : False := by
  have hhu := (mem_distinctR a b c d u).mp hu
  have hhv := (mem_distinctR a b c d v).mp hv
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have nonlow := h.ordinary.nonlow_outside_two f u v hu hv huv hU hV
  apply h.cd_ce_impossible f hF
  · apply nonlow _ (h.ordinary.row_selected h.x h.hx)
    · simp [bit_pair,Ne.symm hhu.2.1,Ne.symm hux]
    · simp [bit_pair,Ne.symm hhv.2.1,Ne.symm hvx]
  · apply nonlow _ (h.cd_ce_middle_without_c f hF h.e h.x h.hex he.1 he.2.1 he.2.2.1 hx.1 hx.2.1 hx.2.2.1)
    · simp [bit_triple,Ne.symm hhu.1,Ne.symm hue,Ne.symm hux]
    · simp [bit_triple,Ne.symm hhv.1,Ne.symm hve,Ne.symm hvx]
  · apply nonlow _ (h.cd_ce_middle_without_c f hF d h.x (Ne.symm hx.2.2.2)
      (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd) (Ne.symm h.ordinary.outer.hcd)
      hx.1 hx.2.1 hx.2.2.1)
    · simp [bit_triple,Ne.symm hhu.1,Ne.symm hhu.2.2.2,Ne.symm hux]
    · simp [bit_triple,Ne.symm hhv.1,Ne.symm hhv.2.2.2,Ne.symm hvx]

theorem cd_ce_false (f : MissingAtNeighbor p a b) (hF : f.F={{c,d},{c,h.e}}) : False := by
  obtain ⟨u,v,huv,hu,hue,hux,huy,hv,hve,hvx,hvy⟩ := h.two_clean_indices
  have good (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y) :
      OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d k := by
    apply h.clean_isolated_good f k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    rw [hF]
    intro s hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp [hh.2.2.1,hh.2.2.2,hke]
  exact h.cd_ce_two_rows_false f hF u v hu hv huv hue hux hve hvx
    (good u hu hue hux huy) (good v hv hve hvx hvy)

theorem cd_de_false (f : MissingAtNeighbor p a b) (hF : f.F={{c,d},{d,h.e}}) : False := by
  apply h.mirror.cd_ce_false f.mirror
  change f.F={{d,c},{d,h.e}}
  simpa only [Finset.pair_comm d c] using hF

end SharedOuterConfig
#print axioms SharedOuterConfig.cd_ce_false
#print axioms SharedOuterConfig.cd_de_false
end
end Snake9
