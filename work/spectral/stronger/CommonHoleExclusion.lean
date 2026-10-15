import CommonHoleMiddleRestrictions
import CommonHoleStarGroups

namespace Snake9
open Finset Classical
noncomputable section

theorem CommonHoleConfig.impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : CommonHoleConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) : False := by
  obtain ⟨hRR,hCD,hdouble⟩ := h.middle_restrictions f hFcard
  have hRR' : ∀i j,i∈distinctR a b c d→j∈distinctR a b c d→i≠j→({i,j}:Finset Coord)∉f.F := by
    intro i j hi hj hij hm
    apply hRR {i,j} hm
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · exact Finset.mem_singleton.mp hk ▸ hj
  apply h.all_active_endpoint_groups_false
  intro k hk hke
  exact h.active_endpoint f hRR' hCD k hk hke (hdouble k hk hke)

#print axioms CommonHoleConfig.impossible
end
end Snake9
