import EqualOuterPairResidual

namespace Snake9

theorem EqualOuterPairConfig.impossible {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : EqualOuterPairConfig p a b c d) (f : MissingAtNeighbor p a b)
    (hFcard : f.F.card=2) : False :=
  h.common_missing_impossible f hFcard (h.middle_hole_forced f hFcard)

#print axioms EqualOuterPairConfig.impossible
end Snake9
