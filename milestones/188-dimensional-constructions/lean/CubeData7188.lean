import LayerJoining
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness7
def Adj (u v : Fin 128) : Prop := (List.range 7).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Fin 128) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
def pathValues : Array Nat := #[0, 1, 3, 7, 6, 14, 12, 13, 29, 25, 27, 26, 18, 50, 51, 49, 53, 37, 36, 100, 68, 69, 85, 81, 80, 88, 72, 73, 75, 79, 95, 94, 86, 118, 119, 103, 99, 98, 106, 122, 123, 121, 125, 124, 60, 56, 40, 41, 43, 47, 63]
def pathVertex (i : Fin 51) : Fin 128 := ⟨pathValues[i.val]! % 128,Nat.mod_lt _ (by decide)⟩
def Row (i : Fin 51) : Prop := ∀ j : Fin 51,
  (pathVertex i = pathVertex j → i=j) ∧
  (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val))
def transitions : Array Nat := #[0, 1, 2, 0, 3, 1, 0, 4, 2, 1, 0, 3, 5, 0, 1, 2, 4, 0, 6, 5, 0, 4, 2, 0, 3, 4, 0, 1, 2, 4, 0, 3, 5, 0, 4, 2, 0, 3, 4, 0, 1, 2, 0, 6, 2, 4, 0, 1, 2, 4]
theorem transitions_agree : ∀ i : Fin 50,
  (pathVertex ⟨i.val+1,by omega⟩).val = Nat.xor (pathVertex ⟨i.val,by omega⟩).val (2^transitions[i.val]!) := by decide +kernel
theorem minimum_crossings : ∀ k : Fin 7, 2 ≤ transitions.toList.count k.val := by decide +kernel
theorem displayed_cut_indices : (List.range 50).filter (fun i => transitions[i]! == 6) = [18, 43] := by decide +kernel
#print axioms transitions_agree
#print axioms minimum_crossings
#print axioms displayed_cut_indices
end Dimensional188.Witness7
