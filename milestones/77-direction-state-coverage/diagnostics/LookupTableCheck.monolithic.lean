import DirectionTables

namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lookupCheck (xs : List (List Nat)) (i : Nat) : Bool :=
  xs.idxOf (xs.getD i []) == i

theorem shape_lookup_checked : allBelow 132 (lookupCheck shapes) = true := by
  decide +kernel

theorem direction_lookup_checked : allBelow 505 (lookupCheck extensions) = true := by
  decide +kernel

def mapCheck (i : Nat) : Bool :=
  (sourceIds.getD i 0 == sourceId i) && (targetIds.getD i 0 == targetId i)

theorem map_checked : allBelow 505 mapCheck = true := by
  decide +kernel

theorem shape_index_getD (i : Nat) (hi : i < 132) :
    shapes.idxOf (shapes.getD i []) = i := by
  have h := allBelow_spec 132 _ shape_lookup_checked i hi
  simpa [lookupCheck] using h

theorem direction_index_getD (i : Nat) (hi : i < 505) :
    extensions.idxOf (extensions.getD i []) = i := by
  have h := allBelow_spec 505 _ direction_lookup_checked i hi
  simpa [lookupCheck] using h

theorem recorded_maps_exact (i : Nat) (hi : i < 505) :
    sourceIds.getD i 0 = sourceId i ∧ targetIds.getD i 0 = targetId i := by
  have h := allBelow_spec 505 _ map_checked i hi
  simpa [mapCheck, Bool.and_eq_true] using h

theorem shape_lookup_unique (i j : Nat) (hi : i < 132) (hj : j < 132)
    (h : shapes.getD i [] = shapes.getD j []) : i = j := by
  have he := congrArg (fun c => shapes.idxOf c) h
  simpa only [shape_index_getD i hi, shape_index_getD j hj] using he

theorem direction_lookup_unique (i j : Nat) (hi : i < 505) (hj : j < 505)
    (h : extensions.getD i [] = extensions.getD j []) : i = j := by
  have he := congrArg (fun c => extensions.idxOf c) h
  simpa only [direction_index_getD i hi, direction_index_getD j hj] using he

#print axioms shape_lookup_checked
#print axioms direction_lookup_checked
#print axioms map_checked
#print axioms shape_index_getD
#print axioms direction_index_getD
#print axioms recorded_maps_exact
#print axioms shape_lookup_unique
#print axioms direction_lookup_unique
end Snake9.Direction77
