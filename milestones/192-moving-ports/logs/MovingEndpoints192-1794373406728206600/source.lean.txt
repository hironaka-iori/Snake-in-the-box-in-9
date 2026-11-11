import EdgeBalance190
import IncidenceBalance190
namespace MovingEndpoints192
open ExchangeAccounting190

theorem edgeCorrection {V : Type} (es : List (V × V))
    (p q : V → Bool) (removedCount addedCount gain lostEnds newEnds : Nat)
    (hsize : addedCount=removedCount+gain)
    (hremoved : incidence es p q + lostEnds=2*removedCount)
    (hadded : incidence es q p + newEnds=2*addedCount)
    (hlength : edges es q=edges es p+gain) :
    edges es (removed q p)+newEnds=edges es (removed p q)+gain+lostEnds := by
  have h := edgeAccounting es p q
  omega

theorem boundaryCorrection {V : Type} (es : List (V × V))
    (p q : V → Bool) (removedCount addedCount gain lostEnds newEnds : Nat)
    (hsize : addedCount=removedCount+gain)
    (hremoved : incidence es p q + lostEnds=2*removedCount)
    (hadded : incidence es q p + newEnds=2*addedCount)
    (hlength : edges es q=edges es p+gain) :
    boundary es q p+lostEnds=boundary es p q+newEnds := by
  have he := edgeCorrection es p q removedCount addedCount gain lostEnds newEnds hsize hremoved hadded hlength
  have hd := incidenceAccounting es p q
  have ha := incidenceAccounting es q p
  omega

theorem componentCorrection {V : Type} (es : List (V × V))
    (p q : V → Bool) (removedCount addedCount gain lostEnds newEnds removedComponents addedComponents : Nat)
    (hsize : addedCount=removedCount+gain)
    (hremoved : incidence es p q + lostEnds=2*removedCount)
    (hadded : incidence es q p + newEnds=2*addedCount)
    (hlength : edges es q=edges es p+gain)
    (hd : removedCount=removedComponents+edges es (removed p q))
    (ha : addedCount=addedComponents+edges es (removed q p)) :
    addedComponents+lostEnds=removedComponents+newEnds := by
  have he := edgeCorrection es p q removedCount addedCount gain lostEnds newEnds hsize hremoved hadded hlength
  omega

#print axioms edgeCorrection
#print axioms boundaryCorrection
#print axioms componentCorrection
end MovingEndpoints192
