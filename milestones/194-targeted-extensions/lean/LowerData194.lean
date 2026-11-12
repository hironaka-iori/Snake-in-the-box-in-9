import LayerJoining
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
def Adj (u v : Fin 128) : Prop := (List.range 7).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Fin 128) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
def oldValues : Array Nat := #[5, 4, 0, 64, 65, 67, 71, 79, 77, 76, 92, 84, 85, 117, 101, 100, 102, 110, 126, 127, 123, 107, 105, 104, 120, 112, 114, 82, 90, 74, 10, 42, 34, 35, 39, 47, 45, 44, 60, 52, 54, 22, 30, 31, 27, 19, 17, 49, 57]
def oldVertex (i : Fin 49) : Fin 128 := ⟨oldValues[i.val]! % 128,Nat.mod_lt _ (by decide)⟩
def oldRow (i : Fin 49) : Prop := ∀ j : Fin 49,
  (oldVertex i=oldVertex j → i=j) ∧
  (i.val<j.val → (Adj (oldVertex i) (oldVertex j) ↔ i.val+1=j.val))
def newValues : Array Nat := #[7, 5, 37, 45, 44, 46, 110, 102, 100, 68, 76, 77, 73, 65, 67, 66, 74, 90, 94, 86, 87, 85, 117, 125, 124, 120, 112, 114, 115, 123, 107, 43, 35, 34, 32, 0, 8, 24, 28, 20, 52, 54, 55, 63, 31, 27, 19, 17, 49, 57]
def newVertex (i : Fin 50) : Fin 128 := ⟨newValues[i.val]! % 128,Nat.mod_lt _ (by decide)⟩
def newRow (i : Fin 50) : Prop := ∀ j : Fin 50,
  (newVertex i=newVertex j → i=j) ∧
  (i.val<j.val → (Adj (newVertex i) (newVertex j) ↔ i.val+1=j.val))
theorem retainedOutside : ∀ i : Fin 49, i.val=0 ∨ 43≤i.val →
  newVertex ⟨i.val+1,by omega⟩ = oldVertex i := by decide +kernel
#print axioms retainedOutside
end Lower194
