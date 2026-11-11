import LayerJoining
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
def Adj (u v : Fin 256) : Prop := (List.range 8).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Fin 256) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
def pathValues : Array Nat := #[0, 1, 3, 7, 15, 13, 12, 28, 30, 62, 46, 38, 36, 52, 116, 124, 108, 109, 111, 103, 119, 55, 183, 167, 175, 173, 172, 188, 184, 56, 40, 41, 43, 59, 187, 155, 153, 137, 136, 138, 202, 194, 192, 193, 209, 211, 243, 227, 235, 233, 249, 253, 245, 229, 228, 230, 238, 254, 250, 122, 106, 98, 96, 97, 113, 49, 177, 161, 160, 162, 178, 50, 18, 82, 80, 88, 72, 73, 75, 91, 95, 223, 207, 205, 204, 220, 212, 214, 150, 134, 132, 133, 149, 21, 85, 69, 68, 70, 78]
def pathVertex (i : Fin 99) : Fin 256 := ⟨pathValues[i.val]! % 256,Nat.mod_lt _ (by decide)⟩
def Row (i : Fin 99) : Prop := ∀ j : Fin 99,
  (pathVertex i = pathVertex j → i=j) ∧
  (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val))
def transitions : Array Nat := #[0, 1, 2, 3, 1, 0, 4, 1, 5, 4, 3, 1, 4, 6, 3, 4, 0, 1, 3, 4, 6, 7, 4, 3, 1, 0, 4, 2, 7, 4, 0, 1, 4, 7, 5, 1, 4, 0, 1, 6, 3, 1, 0, 4, 1, 5, 4, 3, 1, 4, 2, 3, 4, 0, 1, 3, 4, 2, 7, 4, 3, 1, 0, 4, 6, 7, 4, 0, 1, 4, 7, 5, 6, 1, 3, 4, 0, 1, 4, 2, 7, 4, 1, 0, 4, 3, 1, 6, 4, 1, 0, 4, 7, 6, 4, 0, 1, 3]
end Dimensional188.Witness8
