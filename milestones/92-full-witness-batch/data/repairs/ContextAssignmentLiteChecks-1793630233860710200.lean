import ContextAssignmentLiteData
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.ContextLite92

theorem indexed_mem {α : Type} (xs : List α) (i : Nat) (d : α)
    (hi : i < xs.length) : (xs.getD i d,i) ∈ xs.zipIdx := by
  have hi' : i < xs.zipIdx.length := by simpa only [List.length_zipIdx] using hi
  have h := List.getElem_mem hi'
  simpa only [List.getElem_zipIdx,Nat.zero_add,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi,Option.getD_some] using h

theorem source_sizes : sourceShapeIds.length = 505 ∧ compatibilityIds.length = 75 := by
  decide +kernel

theorem fast_checked : fastCheck = true := by decide +kernel

theorem assignmentAt_true (di q : Nat) (hd : di < 505) (hq : q < 75) :
    assignmentAt di q = true := by
  have hd' : di < sourceShapeIds.length := by simpa only [source_sizes.1] using hd
  have hq' : q < compatibilityIds.length := by simpa only [source_sizes.2] using hq
  have hrow := List.all_eq_true.mp fast_checked (sourceShapeIds.getD di 0,di)
    (indexed_mem sourceShapeIds di 0 hd')
  have h := List.all_eq_true.mp hrow (compatibilityIds.getD q 0,q)
    (indexed_mem compatibilityIds q 0 hq')
  simpa only [rowAt,assignmentAt,sourceCompatibleB] using h

#print axioms indexed_mem
#print axioms source_sizes
#print axioms fast_checked
#print axioms assignmentAt_true
end Snake9.ContextLite92
