import ContextAssignmentLiteData
import Mathlib.Tactic

set_option maxRecDepth 100000

namespace Snake9.ContextLite92

def rowCheck (source : Nat × Nat) : Bool :=
  compatibilityIds.zipIdx.all fun history =>
    rowAt source.2 source.1 history.2 history.1

def prefixCheck (n : Nat) : Bool := (sourceShapeIds.zipIdx.take n).all rowCheck

def chunkCheck (start count : Nat) : Bool :=
  ((sourceShapeIds.zipIdx.drop start).take count).all rowCheck

theorem indexed_mem {α : Type} (xs : List α) (i : Nat) (d : α)
    (hi : i < xs.length) : (xs.getD i d,i) ∈ xs.zipIdx := by
  have hi' : i < xs.zipIdx.length := by simpa only [List.length_zipIdx] using hi
  have h := List.getElem_mem hi'
  simpa only [List.getElem_zipIdx,Nat.zero_add,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi,Option.getD_some] using h

theorem source_sizes : sourceShapeIds.length = 505 ∧ compatibilityIds.length = 75 := by
  decide +kernel

theorem prefix_add (start count : Nat) :
    prefixCheck (start+count) = (prefixCheck start && chunkCheck start count) := by
  simp only [prefixCheck,chunkCheck,List.take_add,List.all_append]

theorem prefix_full : prefixCheck 505 = fastCheck := by
  have hlen : sourceShapeIds.zipIdx.length ≤ 505 := by
    simpa only [List.length_zipIdx,source_sizes.1] using (Nat.le_refl 505)
  unfold prefixCheck
  rw [List.take_of_length_le hlen]
  rfl

theorem assignmentAt_of_fast (hfast : fastCheck = true) (di q : Nat)
    (hd : di < 505) (hq : q < 75) : assignmentAt di q = true := by
  have hd' : di < sourceShapeIds.length := by simpa only [source_sizes.1] using hd
  have hq' : q < compatibilityIds.length := by simpa only [source_sizes.2] using hq
  have hrow := (List.all_eq_true (l := sourceShapeIds.zipIdx) (p := rowCheck)).mp
    hfast (sourceShapeIds.getD di 0,di) (indexed_mem sourceShapeIds di 0 hd')
  have h := List.all_eq_true.mp hrow (compatibilityIds.getD q 0,q)
    (indexed_mem compatibilityIds q 0 hq')
  simpa only [rowAt,assignmentAt,sourceCompatibleB] using h

#print axioms indexed_mem
#print axioms source_sizes
#print axioms prefix_add
#print axioms prefix_full
#print axioms assignmentAt_of_fast
end Snake9.ContextLite92
