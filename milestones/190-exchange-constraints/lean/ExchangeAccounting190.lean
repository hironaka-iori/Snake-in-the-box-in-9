import EdgeBalance190
import IncidenceBalance190
namespace ExchangeAccounting190
theorem fixedEndpointExchange {V : Type} (es : List (V × V))
    (s t : V → Bool) (r a gain : Nat)
    (hvertices : a = r + gain)
    (hdeletedDegree : incidence es s t = 2*r)
    (haddedDegree : incidence es t s = 2*a)
    (hedges : edges es t = edges es s + gain) :
    edges es (removed t s) = edges es (removed s t) + gain ∧
    boundary es t s + 2*edges es (removed s t) = 2*r := by
  have h := edgeAccounting es s t
  have hb := incidenceAccounting es t s
  omega

theorem componentAccounting {V : Type} (es : List (V × V))
    (s t : V → Bool) (r a gain c : Nat)
    (hvertices : a = r + gain)
    (hdeletedDegree : incidence es s t = 2*r)
    (haddedDegree : incidence es t s = 2*a)
    (hedges : edges es t = edges es s + gain)
    (hblocks : r = c + edges es (removed s t)) :
    a = c + edges es (removed t s) ∧ boundary es t s = 2*c := by
  have h := fixedEndpointExchange es s t r a gain hvertices hdeletedDegree haddedDegree hedges
  omega

theorem fiveVertexCases (deletedEdges addedEdges components : Nat)
    (h : deletedEdges + components = 5)
    (hpos : 1 ≤ components) (hgain : addedEdges = deletedEdges+2) :
    (deletedEdges=0 ∧ addedEdges=2 ∧ components=5) ∨
    (deletedEdges=1 ∧ addedEdges=3 ∧ components=4) ∨
    (deletedEdges=2 ∧ addedEdges=4 ∧ components=3) ∨
    (deletedEdges=3 ∧ addedEdges=5 ∧ components=2) ∨
    (deletedEdges=4 ∧ addedEdges=6 ∧ components=1) := by omega

#print axioms fixedEndpointExchange
#print axioms componentAccounting
#print axioms fiveVertexCases
end ExchangeAccounting190
