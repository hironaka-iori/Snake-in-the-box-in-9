import OrdinaryEndpointCount
import DisjointOrdinaryDemand

namespace Snake9
open Finset Classical
noncomputable section

theorem OrdinaryOuterConfig.disjoint_impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : OrdinaryOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (hAB : Disjoint h.A h.B) : False := by
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.outer.hab,h.outer.hac,
      h.outer.had,h.outer.hbc,h.outer.hbd,h.outer.hcd]
  have hlo := disjoint_ordinary_endpoint_demand f.F (distinctR a b c d) h.A h.B c d hR hFcard
    f.edge_card h.Acard h.Bcard h.Asub h.Bsub hAB (by simp [distinctR]) (by simp [distinctR]) h.outer.hcd
  have hhi := h.endpoint_demand_bound f
  omega

#print axioms OrdinaryOuterConfig.disjoint_impossible
end
end Snake9
