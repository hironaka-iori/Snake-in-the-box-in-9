import NumericRetention
import RetainedEnumeration

namespace Snake9.Assembly87
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.History78 Snake9.GraphWalk78
open Snake9.Retained87 Snake9.Enumeration87

def rowSource (key : Row) : Nat := edgeSource key.2.1 key.1 key.2.2
def rowTarget (key : Row) : Nat := edgeTarget key.2.1 key.1 key.2.2
def retainedKeep (d q c : Nat) : Bool := numericKeep q d c

/-- The finite coverage and endpoint-column premises are intentionally explicit. -/
theorem actual_saved_edge (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    (rows : Array Row) (U V : Array Nat)
    (hcover : RetentionCover retainedKeep rows.toList)
    (hU : U.toList = rows.toList.map rowSource)
    (hV : V.toList = rows.toList.map rowTarget)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    ∃ i : Nat,
      rows.toList[i]? = some (directionId p r, actualHistory p r, sixCode p r) ∧
      U.toList[i]? = some (actualState p r) ∧
      V.toList[i]? = some (actualState p (r+1)) := by
  obtain ⟨hq,hd,hc⟩ := (actual_range_compatible p r hr).1
  obtain ⟨i,hi⟩ := covering_row_index retainedKeep rows hcover
    (directionId p r) (actualHistory p r) (sixCode p r) hd hq hc
    (actual_numeric_keep h235 h236 p r hr)
  have endpoints := indexed_endpoint_maps rows.toList rowSource rowTarget i _ hi
  simp only [rowSource, rowTarget] at endpoints
  rw [actual_source_state p r hr, actual_target_state p r hr] at endpoints
  exact ⟨i,hi,by simpa only [hU,hV] using endpoints⟩

/-- Every step of the actual state sequence has an in-bounds saved edge index. -/
theorem actual_saved_walk (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    (rows : Array Row) (U V : Array Nat)
    (hcover : RetentionCover retainedKeep rows.toList)
    (hU : U.toList = rows.toList.map rowSource)
    (hV : V.toList = rows.toList.map rowTarget)
    {m : Nat} (p : Snake m) :
    ∃ edge : Fin (m-8) → Fin rows.size, ∀ i,
      U.toList[(edge i).val]? = some (actualState p i.val) ∧
      V.toList[(edge i).val]? = some (actualState p (i.val+1)) := by
  classical
  have step (i : Fin (m-8)) := actual_saved_edge h235 h236 rows U V hcover hU hV
    p i.val (by have h := i.isLt; omega)
  choose index hindex using step
  have hbound (i : Fin (m-8)) : index i < rows.size := by
    have h := (List.getElem?_eq_some_iff.mp (hindex i).1).choose
    simpa using h
  exact ⟨fun i => ⟨index i, hbound i⟩,fun i => (hindex i).2⟩

#print axioms actual_saved_edge
#print axioms actual_saved_walk
end Snake9.Assembly87
