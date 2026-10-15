import SharedCleanRows

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem core_internal (f : MissingAtNeighbor p a b)
    (hF : ∀S∈f.F,S⊆{c,d,h.e,h.x,h.y}) (w : Vertex) (hw : InPath p w)
    (hbits : ∀k∈distinctR a b c d,k≠h.e → k≠h.x → k≠h.y → w.val.testBit k.val=false) :
    ¬AtMostOneNeighbor p w := by
  obtain ⟨u,v,huv,hu,hue,hux,huy,hv,hve,hvx,hvy⟩ := h.two_clean_indices
  have good (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y) :
      OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d k := by
    apply h.clean_isolated_good f k hk hke hkx hky
    intro s hs hks
    have hh := (mem_distinctR a b c d k).mp hk
    have hb := hF s hs hks
    simpa [hh.2.2.1,hh.2.2.2,hke,hkx,hky] using hb
  exact h.ordinary.nonlow_outside_two f u v hu hv huv
    (good u hu hue hux huy) (good v hv hve hvx hvy) w hw
    (hbits u hu hue hux huy) (hbits v hv hve hvx hvy)

end SharedOuterConfig
#print axioms SharedOuterConfig.core_internal
end
end Snake9
