import LookupChunk00
import LookupChunk01
import LookupChunk02
import LookupChunk03
import LookupChunk04
import LookupChunk05
namespace Snake9.Direction77
open Snake9.WindowAutomaton
theorem direction_partial_0 : allBelow 0 (lookupCheck extensions) = true := rfl
theorem direction_partial_100 : allBelow 100 (lookupCheck extensions) = true := by
  calc allBelow 100 (lookupCheck extensions) = (allBelow 0 (lookupCheck extensions) &&
      allBelow 100 (fun i => (lookupCheck extensions) (0+i))) := allBelow_add 0 100 _
    _ = true := by rw [direction_partial_0, direction_chunk_0]; rfl
theorem direction_partial_200 : allBelow 200 (lookupCheck extensions) = true := by
  calc allBelow 200 (lookupCheck extensions) = (allBelow 100 (lookupCheck extensions) &&
      allBelow 100 (fun i => (lookupCheck extensions) (100+i))) := allBelow_add 100 100 _
    _ = true := by rw [direction_partial_100, direction_chunk_1]; rfl
theorem direction_partial_300 : allBelow 300 (lookupCheck extensions) = true := by
  calc allBelow 300 (lookupCheck extensions) = (allBelow 200 (lookupCheck extensions) &&
      allBelow 100 (fun i => (lookupCheck extensions) (200+i))) := allBelow_add 200 100 _
    _ = true := by rw [direction_partial_200, direction_chunk_2]; rfl
theorem direction_partial_400 : allBelow 400 (lookupCheck extensions) = true := by
  calc allBelow 400 (lookupCheck extensions) = (allBelow 300 (lookupCheck extensions) &&
      allBelow 100 (fun i => (lookupCheck extensions) (300+i))) := allBelow_add 300 100 _
    _ = true := by rw [direction_partial_300, direction_chunk_3]; rfl
theorem direction_partial_500 : allBelow 500 (lookupCheck extensions) = true := by
  calc allBelow 500 (lookupCheck extensions) = (allBelow 400 (lookupCheck extensions) &&
      allBelow 100 (fun i => (lookupCheck extensions) (400+i))) := allBelow_add 400 100 _
    _ = true := by rw [direction_partial_400, direction_chunk_4]; rfl
theorem direction_partial_505 : allBelow 505 (lookupCheck extensions) = true := by
  calc allBelow 505 (lookupCheck extensions) = (allBelow 500 (lookupCheck extensions) &&
      allBelow 5 (fun i => (lookupCheck extensions) (500+i))) := allBelow_add 500 5 _
    _ = true := by rw [direction_partial_500, direction_chunk_5]; rfl
theorem maps_partial_0 : allBelow 0 (mapCheck) = true := rfl
theorem maps_partial_100 : allBelow 100 (mapCheck) = true := by
  calc allBelow 100 (mapCheck) = (allBelow 0 (mapCheck) &&
      allBelow 100 (fun i => (mapCheck) (0+i))) := allBelow_add 0 100 _
    _ = true := by rw [maps_partial_0, maps_chunk_0]; rfl
theorem maps_partial_200 : allBelow 200 (mapCheck) = true := by
  calc allBelow 200 (mapCheck) = (allBelow 100 (mapCheck) &&
      allBelow 100 (fun i => (mapCheck) (100+i))) := allBelow_add 100 100 _
    _ = true := by rw [maps_partial_100, maps_chunk_1]; rfl
theorem maps_partial_300 : allBelow 300 (mapCheck) = true := by
  calc allBelow 300 (mapCheck) = (allBelow 200 (mapCheck) &&
      allBelow 100 (fun i => (mapCheck) (200+i))) := allBelow_add 200 100 _
    _ = true := by rw [maps_partial_200, maps_chunk_2]; rfl
theorem maps_partial_400 : allBelow 400 (mapCheck) = true := by
  calc allBelow 400 (mapCheck) = (allBelow 300 (mapCheck) &&
      allBelow 100 (fun i => (mapCheck) (300+i))) := allBelow_add 300 100 _
    _ = true := by rw [maps_partial_300, maps_chunk_3]; rfl
theorem maps_partial_500 : allBelow 500 (mapCheck) = true := by
  calc allBelow 500 (mapCheck) = (allBelow 400 (mapCheck) &&
      allBelow 100 (fun i => (mapCheck) (400+i))) := allBelow_add 400 100 _
    _ = true := by rw [maps_partial_400, maps_chunk_4]; rfl
theorem maps_partial_505 : allBelow 505 (mapCheck) = true := by
  calc allBelow 505 (mapCheck) = (allBelow 500 (mapCheck) &&
      allBelow 5 (fun i => (mapCheck) (500+i))) := allBelow_add 500 5 _
    _ = true := by rw [maps_partial_500, maps_chunk_5]; rfl
theorem shape_lookup_checked : allBelow 132 (lookupCheck shapes) = true := shape_roundtrip
theorem direction_lookup_checked : allBelow 505 (lookupCheck extensions) = true := direction_partial_505
theorem map_checked : allBelow 505 mapCheck = true := maps_partial_505

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
