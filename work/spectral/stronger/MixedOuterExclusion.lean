import MixedEndpointCounting
import MixedOrdinaryEndpoints

namespace Snake9
open Finset Classical
noncomputable section

theorem MixedOuterConfig.impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : MixedOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) : False := by
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.left.outer.hab,h.left.outer.hac,
      h.left.outer.had,h.left.outer.hbc,h.left.outer.hbd,h.left.outer.hcd]
  have hlo := two_edge_endpoint_demand (distinctR a b c d) f.F hR hFcard f.edge_card
  have hhi := isolated_ordinary_resource_count p a b c d h.left.e f.F f.edge_card
    (h.isolated_endpoint f hFcard) (h.left.missing_ordinary_endpoint f hFcard (h.isolated_endpoint f hFcard))
  omega

#print axioms MixedOuterConfig.impossible
end
end Snake9
