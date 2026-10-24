import LocalWindowTags
import LocalWindowBridge

namespace Snake9.ExteriorTurn.Sharp
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def values : Array Nat := #[10, 8, 0, 1, 3, 7, 15, 31, 30, 22, 20, 52, 60, 44, 46, 38, 34, 50, 51, 59, 43, 41, 105, 73, 75, 331, 267, 265, 393, 137, 139, 155, 154, 146, 130, 134, 142, 140, 156, 157, 149, 213, 85, 87, 83, 211, 195, 199, 207, 223, 222, 214, 246, 182, 190, 191, 175, 167, 163, 161, 177, 185, 184, 440, 432, 434, 498, 506, 510, 511, 509, 505, 497, 465, 449, 453, 461, 333, 349, 351, 350, 342, 374, 310, 318, 319, 317, 309, 277, 279, 275, 403, 387, 391, 399, 415, 414, 406, 404, 468, 500, 484, 492, 488, 456, 458, 394, 426, 427, 491, 235, 234, 226, 224, 96, 352, 288, 289, 291, 355, 99, 103, 111, 127, 126, 122, 90, 88, 92, 76, 78, 70, 66, 322, 258, 262, 270, 268, 284, 280, 282]
def vertex (i : Fin 141) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem distinct : ∀ i j : Fin 141, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin 141, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake 140 := ⟨vertex, distinct, induced⟩
theorem window_directions : ∀ j : Fin 8,
    dir witness (2+j.val) = ([0, 1, 2, 3, 4, 0, 3, 1] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
theorem pair_counts : coreAlpha witness 4 = 4 ∧
    coreAlpha witness 8 = 3 := by decide +kernel
theorem attains : ∃ p : Snake 140,
    coreAlpha p 4 + coreAlpha p 8 = 7 ∧
    (∀ j : Fin 8, dir p (2+j.val) = ([0, 1, 2, 3, 4, 0, 3, 1] : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [pair_counts.1,pair_counts.2]

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms attains
end Snake9.ExteriorTurn.Sharp
