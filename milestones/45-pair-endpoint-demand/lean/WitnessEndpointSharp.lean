import EndpointDistance
namespace Snake9.EndpointSharp
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def values : Array Nat := #[90, 122, 126, 118, 119, 87, 83, 81, 80, 112, 368, 370, 338, 342, 350, 351, 349, 93, 92, 76, 78, 70, 66, 98, 99, 97, 105, 73, 75, 331, 323, 321, 320, 328, 344, 472, 476, 460, 462, 458, 202, 234, 235, 251, 243, 499, 497, 505, 509, 253, 245, 244, 212, 214, 222, 223, 207, 199, 195, 193, 192, 224, 480, 488, 424, 296, 297, 301, 45, 61, 60, 56, 24, 8, 0, 1, 3, 7, 15, 31, 30, 22, 20, 276, 284, 268, 270, 262, 258, 290, 291, 295, 311, 310, 318, 314, 282, 283, 275, 273, 305, 49, 51, 59, 43, 42, 46, 38, 36, 164, 420, 422, 486, 487, 485, 453, 389, 391, 387, 395, 139, 137, 169, 161, 163, 162, 130, 134, 142, 140, 156, 157, 413, 415, 414, 406, 402, 434, 432, 176, 144, 145, 147, 151, 183, 191, 190, 186, 154]
def vertex (i : Fin 149) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem distinct : ∀ i j : Fin 149, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin 149, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake 148 := ⟨vertex, distinct, induced⟩
theorem window_directions : ∀ j : Fin 8,
    dir witness (74+j.val) = ([0,1,2,3,4,0,3,1] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
theorem pair_counts : coreAlpha witness 76 = 5 ∧ coreAlpha witness 80 = 3 := by decide +kernel
theorem endpoint_distances :
    EndpointPair451.hamming (vx witness 76) (vx witness 0) = 4 ∧
    EndpointPair451.hamming (vx witness 76) (vx witness 148) = 4 := by decide +kernel
#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms endpoint_distances
end Snake9.EndpointSharp
