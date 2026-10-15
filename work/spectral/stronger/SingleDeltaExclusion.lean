import SingleDeltaMiddle
import SingleDeltaEndpoints

namespace Snake9

theorem SingleDeltaConfig.impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : SingleDeltaConfig p a b c d) (f : MissingAtNeighbor p a b)
    (hFcard : f.F.card=2) : False :=
  h.middle_impossible f hFcard h.triple_not_low

#print axioms SingleDeltaConfig.impossible
end Snake9
