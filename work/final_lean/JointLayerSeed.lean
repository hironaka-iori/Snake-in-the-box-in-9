import IntegerLayerBridge

namespace JointLayerSeed
open LayerJoining
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def leftValues : Array Nat := #[48, 52, 36, 38, 34, 42, 43, 41, 45, 61, 63, 55, 51, 19, 27, 25, 24, 88, 80, 84, 68, 70, 66, 67, 75, 73, 77, 93, 95, 87, 215, 199, 197, 193, 209, 217, 219, 218, 202, 206, 204, 220, 252, 253, 237, 233, 235, 227, 226, 224, 96, 104, 108, 110, 111, 103, 101, 117, 113, 121, 123, 122, 114, 118, 246, 182, 178, 186, 187, 185, 177, 161, 165, 167, 175, 174, 172, 168, 136, 137, 139, 131, 130, 134, 132, 148, 149, 157, 159, 158, 30, 14, 15, 7, 5, 1, 0]
def leftVertex (i : Fin 97) : Snake8.Vertex :=
  ⟨leftValues[i.val]! % 256, Nat.mod_lt _ (by decide)⟩

theorem left_distinct : ∀ i j : Fin 97, leftVertex i=leftVertex j → i=j := by decide
theorem left_induced : ∀ i j : Fin 97, i.val<j.val →
    (Snake8.Adj (leftVertex i) (leftVertex j) ↔ i.val+1=j.val) := by decide

def leftPath : Snake8.Snake 96 := ⟨leftVertex,left_distinct,left_induced⟩

def rightValues : Array Nat := #[0, 2, 3, 11, 9, 13, 29, 28, 156, 140, 142, 138, 154, 155, 153, 145, 129, 133, 135, 151, 183, 191, 189, 173, 169, 171, 163, 162, 166, 164, 180, 176, 184, 248, 120, 112, 116, 100, 102, 98, 106, 107, 105, 109, 125, 127, 119, 115, 243, 241, 225, 229, 231, 239, 238, 254, 222, 223, 221, 213, 212, 196, 198, 194, 195, 203, 201, 200, 72, 76, 78, 79, 71, 69, 65, 81, 89, 91, 90, 82, 86, 22, 54, 50, 58, 59, 57, 49, 53, 37, 39, 47, 46, 44, 40]
def rightVertex (i : Fin 95) : Snake8.Vertex :=
  ⟨rightValues[i.val]! % 256, Nat.mod_lt _ (by decide)⟩

theorem right_distinct : ∀ i j : Fin 95, rightVertex i=rightVertex j → i=j := by decide
theorem right_induced : ∀ i j : Fin 95, i.val<j.val →
    (Snake8.Adj (rightVertex i) (rightVertex j) ↔ i.val+1=j.val) := by decide

def rightPath : Snake8.Snake 94 := ⟨rightVertex,right_distinct,right_induced⟩

theorem compatible : Compatible leftPath rightPath := by
  change ∀ i : Fin 97, ∀ j : Fin 95, leftVertex i=rightVertex j ↔ i.val=96 ∧ j.val=0
  decide

theorem normalized_join :
    (leftPath.vertex ⟨96,by decide⟩).val=0 ∧
    (rightPath.vertex ⟨0,by decide⟩).val=0 ∧
    (leftPath.vertex ⟨95,by decide⟩).val=1 ∧
    (rightPath.vertex ⟨1,by decide⟩).val=2 := by decide

def joined : Snake9.Snake 191 := IntegerLayerBridge.join leftPath rightPath compatible

theorem adjacent_to_join_distinct {V : Type} {R : V → V → Prop} {a b : Nat}
    (p : InducedPath V R a) (q : InducedPath V R b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : Compatible p q) :
    p.vertex ⟨a-1,by omega⟩ ≠ q.vertex ⟨1,by omega⟩ := by
  intro he
  have h := (hc ⟨a-1,by omega⟩ ⟨1,by omega⟩).mp he
  simp only at h
  omega

#print axioms compatible
#print axioms normalized_join
#print axioms joined
#print axioms adjacent_to_join_distinct
end JointLayerSeed
