import ActualDirectionIds
import HistoryCompatibilityData
import NumericHistory

namespace Snake9.Direction77
open Snake9.History75 Snake9.History77

def readDirections {m : Nat} (p : Snake m) (r : Nat) : List Nat :=
  (List.range r).map (directionId p)

def actualHistory {m : Nat} (p : Snake m) (r : Nat) : Nat :=
  historyIndex (readDirections p r)

theorem readDirections_succ {m : Nat} (p : Snake m) (r : Nat) :
    readDirections p (r+1) = readDirections p r ++ [directionId p r] := by
  simp [readDirections, List.range_succ, List.map_append]

theorem actual_history_initial {m : Nat} (p : Snake m) : actualHistory p 0 = 0 := by
  exact history_index_empty

theorem actual_history_lt {m : Nat} (p : Snake m) (r : Nat) : actualHistory p r < 75 :=
  history_index_lt _

theorem stored_nonempty_of_index (w : List Nat) (hq : historyIndex w ≠ 0) :
    run prefixes w ≠ [] := by
  intro hn
  apply hq
  unfold historyIndex
  rw [hn]
  rfl

theorem compatible_after_append (w : List Nat) (a : Nat)
    (hq : historyIndex (w ++ [a]) ≠ 0) :
    compatibleShape (historyIndex (w ++ [a])) = targetId a := by
  unfold compatibleShape
  rw [history_decode]
  have hn := stored_nonempty_of_index (w ++ [a]) hq
  have hl := stored_append_last w a hn
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hn,
    Option.getD_some, hl]

theorem actual_history_shape_succ {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) (hq : actualHistory p (r+1) ≠ 0) :
    compatibleShape (actualHistory p (r+1)) = shapeId p (r+1) := by
  have he : actualHistory p (r+1) = historyIndex (readDirections p r ++ [directionId p r]) := by
    unfold actualHistory
    rw [readDirections_succ]
  rw [he] at hq ⊢
  rw [compatible_after_append _ _ hq, target_id_exact p r hr]

theorem actual_history_shape {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+8 ≤ m) (hq : actualHistory p r ≠ 0) :
    compatibleShape (actualHistory p r) = shapeId p r := by
  cases r with
  | zero => exact False.elim (hq (actual_history_initial p))
  | succ r => exact actual_history_shape_succ p r (by omega) hq

theorem actual_source_history_filter {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) (hq : actualHistory p r ≠ 0) :
    recordedCompatible.getD (actualHistory p r) 0 = sourceId (directionId p r) := by
  rw [recorded_compatible_exact _ hq (actual_history_lt p r),
    actual_history_shape p r (by omega) hq, source_id_exact p r hr]

theorem actual_target_history_filter {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) (hq : actualHistory p (r+1) ≠ 0) :
    recordedCompatible.getD (actualHistory p (r+1)) 0 = targetId (directionId p r) := by
  rw [recorded_compatible_exact _ hq (actual_history_lt p (r+1)),
    actual_history_shape_succ p r hr hq, target_id_exact p r hr]

#print axioms readDirections_succ
#print axioms actual_history_initial
#print axioms actual_history_lt
#print axioms stored_nonempty_of_index
#print axioms compatible_after_append
#print axioms actual_history_shape_succ
#print axioms actual_history_shape
#print axioms actual_source_history_filter
#print axioms actual_target_history_filter
end Snake9.Direction77
