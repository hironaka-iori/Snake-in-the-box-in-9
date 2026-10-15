import SharedMissingRightFamilies
import SharedFiniteClassification

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem cx_B_false (f : MissingAtNeighbor p a b)
    (hF : f.F={{c,h.x},{h.e,h.y}}) : False := by
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  exact h.missing_right_family_impossible f {c,h.x}
    (by simpa only [Finset.pair_comm ({c,h.x}:Finset Coord) {h.e,h.y}] using hF)
    (by simp [Finset.subset_iff])
    (by simp [finite_pair_eq_iff,hx.2.2.2,hx.2.2.1,Ne.symm h.ordinary.outer.hcd])
    (by simp [finite_pair_eq_iff,Ne.symm h.hex,hx.2.2.1])

theorem dx_B_false (f : MissingAtNeighbor p a b)
    (hF : f.F={{d,h.x},{h.e,h.y}}) : False := by
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  exact h.missing_right_family_impossible f {d,h.x}
    (by simpa only [Finset.pair_comm ({d,h.x}:Finset Coord) {h.e,h.y}] using hF)
    (by simp [Finset.subset_iff])
    (by simp [finite_pair_eq_iff,Ne.symm h.ordinary.outer.hcd,hx.2.2.1])
    (by simp [finite_pair_eq_iff,Ne.symm h.ordinary.outer.hcd,hx.2.2.1])

theorem cy_A_false (f : MissingAtNeighbor p a b)
    (hF : f.F={{c,h.y},{h.e,h.x}}) : False := by
  exact h.mirror.dx_B_false f.mirror hF

theorem dy_A_false (f : MissingAtNeighbor p a b)
    (hF : f.F={{d,h.y},{h.e,h.x}}) : False := by
  exact h.mirror.cx_B_false f.mirror hF

theorem A_B_false (f : MissingAtNeighbor p a b)
    (hF : f.F={{h.e,h.x},{h.e,h.y}}) : False := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  exact h.missing_right_family_impossible f {h.e,h.x}
    (by simpa only [Finset.pair_comm ({h.e,h.x}:Finset Coord) {h.e,h.y}] using hF)
    (by simp [Finset.subset_iff])
    (by simp [finite_pair_eq_iff,he.2.2.1,he.2.2.2])
    (by simp [finite_pair_eq_iff,he.2.2.1,hx.2.2.1])

end SharedOuterConfig
#print axioms SharedOuterConfig.cx_B_false
#print axioms SharedOuterConfig.dx_B_false
#print axioms SharedOuterConfig.cy_A_false
#print axioms SharedOuterConfig.dy_A_false
#print axioms SharedOuterConfig.A_B_false
end
end Snake9
