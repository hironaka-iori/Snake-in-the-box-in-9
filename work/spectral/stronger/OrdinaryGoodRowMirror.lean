import SharedOuterBase
import OrdinaryOuterCountingDefs

namespace Snake9
open Finset Classical
noncomputable section

theorem ordinary_good_row_mirror (F : Finset (Finset Coord)) (R A B : Finset Coord)
    (c d k : Coord) (h : OrdinaryGoodRow F R A B c d k) :
    OrdinaryGoodRow F R B A d c k := by
  have swap (s : Coord) (hs : OrdinaryPartnerClear F R A B k s) :
      OrdinaryPartnerClear F R B A k s := by
    intro r hr hh
    exact hs r hr hh.symm
  refine ⟨h.1,?_⟩
  rcases h.2 with hh | hh
  · exact Or.inl ⟨swap d hh.2,swap c hh.1⟩
  · refine Or.inr ⟨?_,?_⟩
    · simpa only [Finset.pair_comm d c] using hh.1
    · rcases hh.2 with hc | hd
      · exact Or.inr (swap c hc)
      · exact Or.inl (swap d hd)

namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)

theorem mirror_good_row (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : OrdinaryGoodRow f.F (distinctR a b c d) h.A h.B c d k) :
    OrdinaryGoodRow f.mirror.F (distinctR b a d c) h.mirror.A h.mirror.B d c k := by
  have hR : distinctR b a d c=distinctR a b c d := by
    ext r; simp only [mem_distinctR]; tauto
  change OrdinaryGoodRow f.F (distinctR b a d c) h.B h.A d c k
  rw [hR]
  exact ordinary_good_row_mirror _ _ _ _ _ _ _ hk

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.mirror_good_row
end
end Snake9
