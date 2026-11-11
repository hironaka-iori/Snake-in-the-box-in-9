import LayerJoining
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness6
def Adj (u v : Fin 64) : Prop := (List.range 6).any (fun k => v.val == Nat.xor u.val (2^k)) = true
instance (u v : Fin 64) : Decidable (Adj u v) := inferInstanceAs (Decidable (_ = true))
def pathValues : Array Nat := #[0, 1, 3, 7, 15, 13, 12, 28, 20, 21, 53, 37, 36, 38, 46, 62, 63, 59, 43, 41, 40, 56, 48, 50, 18, 26, 10]
def pathVertex (i : Fin 27) : Fin 64 :=
  ⟨pathValues[i.val]! % 64,Nat.mod_lt _ (by decide)⟩
theorem path_distinct : ∀ i j, pathVertex i = pathVertex j → i=j := by decide +kernel
theorem path_induced : ∀ i j, i.val < j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val) := by decide +kernel
def path : LayerJoining.InducedPath (Fin 64) Adj 26 := ⟨pathVertex,path_distinct,path_induced⟩
#print axioms path_distinct
#print axioms path_induced

def transitions : Array Nat := #[0, 1, 2, 3, 1, 0, 4, 3, 0, 5, 4, 0, 1, 3, 4, 0, 2, 4, 1, 0, 4, 3, 1, 5, 3, 4]
theorem transitions_agree : ∀ i : Fin 26,
  (pathVertex ⟨i.val+1,by omega⟩).val = Nat.xor (pathVertex ⟨i.val,by omega⟩).val (2^transitions[i.val]!) := by decide +kernel
theorem minimum_crossings : ∀ k : Fin 6, 2 ≤ transitions.toList.count k.val := by decide +kernel
theorem displayed_cut_indices : (List.range 26).filter (fun i => transitions[i]! == 2) = [2, 16] := by decide +kernel
#print axioms transitions_agree
#print axioms minimum_crossings
#print axioms displayed_cut_indices
end Dimensional188.Witness6
