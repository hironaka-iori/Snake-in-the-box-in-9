import GeneralEndpointGroups
import ThreeMissingClassification

namespace Snake9
set_option maxHeartbeats 1000000

namespace OneTwoRoot
theorem three_missing_impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : OneTwoRoot p a b c d) (f : MissingAtNeighbor p a c) (hcard : f.F.card=3) : False := by
  rcases three_missing_classification f.F a b c d h.hab h.hac h.had h.hbc h.hbd h.hcd
    hcard f.edge_card f.avoids with ⟨j,hji,hj⟩ | ⟨u,v,huv,hu,hv,hd,hiu,_⟩
  · exact h.three_good_indices_false f j hji hj
  · exact h.two_good_isolated_false f u v huv hu hv hd hiu
end OneTwoRoot

#print axioms OneTwoRoot.three_missing_impossible
end Snake9
