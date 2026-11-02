import DirectionCoverage
import WindowStateShift
import NumericHistory

namespace Snake9.Direction77
open Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeAdapter73 Snake9.GraphInterpretation74

def directionId {m : Nat} (p : Snake m) (r : Nat) : Nat :=
  extensions.idxOf (canon (dsOf p r 9))

def shapeId {m : Nat} (p : Snake m) (r : Nat) : Nat :=
  shapes.idxOf (canon (dsOf p r 8))

theorem actual_eight_mem {m : Nat} (p : Snake m) (r : Nat) (hr : r+8 ≤ m) :
    canon (dsOf p r 8) ∈ shapes := by
  have h := snake_eight_coverage p r hr
  rwa [blockList_eq_dsOf p r 8 hr] at h

theorem actual_nine_mem {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    canon (dsOf p r 9) ∈ extensions := by
  have h := snake_nine_coverage p r hr
  rwa [blockList_eq_dsOf p r 9 hr] at h

theorem directionId_lt {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    directionId p r < 505 := by
  have h := List.idxOf_lt_length (actual_nine_mem p r hr)
  simpa only [directionId, extensions_length] using h

theorem shapeId_lt {m : Nat} (p : Snake m) (r : Nat) (hr : r+8 ≤ m) :
    shapeId p r < 132 := by
  have h := List.idxOf_lt_length (actual_eight_mem p r hr)
  simpa only [shapeId, shapes_length] using h

theorem direction_decode {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    extensions.getD (directionId p r) [] = canon (dsOf p r 9) := by
  exact Snake9.History77.dictionary_index_decode (actual_nine_mem p r hr) []

theorem shape_decode {m : Nat} (p : Snake m) (r : Nat) (hr : r+8 ≤ m) :
    shapes.getD (shapeId p r) [] = canon (dsOf p r 8) := by
  exact Snake9.History77.dictionary_index_decode (actual_eight_mem p r hr) []

theorem source_id_exact {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    sourceId (directionId p r) = shapeId p r := by
  unfold sourceId
  rw [direction_decode p r hr, canonical_nine_source p r hr]
  rfl

theorem target_id_exact {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    targetId (directionId p r) = shapeId p (r+1) := by
  unfold targetId
  rw [direction_decode p r hr, canonical_nine_target p r hr]
  rfl

theorem adjacent_direction_ids {m : Nat} (p : Snake m) (r : Nat) (hr : r+10 ≤ m) :
    targetId (directionId p r) = sourceId (directionId p (r+1)) := by
  rw [target_id_exact p r (by omega), source_id_exact p (r+1) (by omega)]

/-- All eight-transition states, including the terminal state. -/
def actualShapeState {m : Nat} (p : Snake m) (i : Fin (m-7)) : Fin 132 :=
  ⟨shapeId p i.val, shapeId_lt p i.val (by have h := i.isLt; omega)⟩

/-- The nine-transition IDs along the actual path. -/
def actualDirectionEdge {m : Nat} (p : Snake m) (i : Fin (m-8)) : Fin 505 :=
  ⟨directionId p i.val, directionId_lt p i.val (by have h := i.isLt; omega)⟩

theorem actual_direction_walk {m : Nat} (p : Snake m) (i : Fin (m-8)) :
    sourceId (actualDirectionEdge p i).val =
      (actualShapeState p ⟨i.val, by have h := i.isLt; omega⟩).val ∧
    targetId (actualDirectionEdge p i).val =
      (actualShapeState p ⟨i.val+1, by have h := i.isLt; omega⟩).val := by
  have hr : i.val+9 ≤ m := by have h := i.isLt; omega
  exact ⟨source_id_exact p i.val hr, target_id_exact p i.val hr⟩

#print axioms actual_eight_mem
#print axioms actual_nine_mem
#print axioms directionId_lt
#print axioms shapeId_lt
#print axioms direction_decode
#print axioms shape_decode
#print axioms source_id_exact
#print axioms target_id_exact
#print axioms adjacent_direction_ids
#print axioms actual_direction_walk
end Snake9.Direction77
