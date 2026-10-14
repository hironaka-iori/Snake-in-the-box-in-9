import LayerJoining

namespace Snake8
abbrev Vertex := Fin 256
def Adj (u v : Vertex) : Prop :=
  (List.range 8).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Vertex) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
abbrev Snake := LayerJoining.InducedPath Vertex Adj
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessValues : Array Nat := #[0, 1, 3, 7, 15, 13, 12, 28, 30, 62, 46, 38, 36, 52, 116, 124, 108, 109, 111, 103, 119, 55, 183, 167, 175, 173, 172, 188, 184, 56, 40, 41, 43, 59, 187, 155, 153, 137, 136, 138, 202, 194, 192, 193, 209, 211, 243, 227, 235, 233, 249, 253, 245, 229, 228, 230, 238, 254, 250, 122, 106, 98, 96, 97, 113, 49, 177, 161, 160, 162, 178, 50, 18, 82, 80, 88, 72, 73, 75, 91, 95, 223, 207, 205, 204, 220, 212, 214, 150, 134, 132, 133, 149, 21, 85, 69, 68, 70, 78]
def witnessVertex (i : Fin 99) : Vertex :=
  ⟨witnessValues[i.val]! % 256, Nat.mod_lt _ (by decide)⟩
theorem witness_distinct :
    ∀ i j : Fin 99, witnessVertex i = witnessVertex j → i = j := by decide
theorem witness_induced :
    ∀ i j : Fin 99, i.val < j.val →
      (Adj (witnessVertex i) (witnessVertex j) ↔ i.val+1=j.val) := by decide
def witness : Snake 98 := ⟨witnessVertex, witness_distinct, witness_induced⟩
theorem lower_bound : Nonempty (Snake 98) := ⟨witness⟩
#print axioms witness_distinct
#print axioms witness_induced
#print axioms lower_bound
end Snake8
