import LocalWindowTags
import LocalWindowBridge

namespace Snake9.ExteriorTurn.Short
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def values : Array Nat := #[161, 160, 416, 420, 436, 438, 434, 402, 400, 144, 145, 147, 151, 407, 415, 413, 157, 156, 158, 142, 134, 132, 133, 389, 385, 393, 137, 136, 200, 192, 193, 195, 199, 207, 223, 219, 217, 249, 505, 509, 511, 510, 506, 474, 472, 344, 336, 80, 81, 83, 87, 343, 351, 349, 93, 92, 94, 90, 74, 75, 73, 329, 321, 325, 69, 68, 70, 326, 322, 258, 256, 0, 1, 3, 7, 15, 31, 27, 25, 281, 273, 277, 21, 20, 22, 278, 286, 284, 268, 332, 460, 452, 468, 212, 214, 210, 242, 243, 499, 371, 379, 123, 127, 111, 103, 99, 97, 96, 352, 356, 372, 373, 117, 245, 229, 228, 230, 486, 487, 423, 419, 291, 289, 293, 37, 36, 38, 46, 62, 60, 61, 317, 319, 311, 55, 51, 49, 48, 304, 312, 296, 40, 41, 43, 171, 187, 191]
def vertex (i : Fin 147) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem distinct : ∀ i j : Fin 147, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin 147, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake 146 := ⟨vertex, distinct, induced⟩
theorem window_directions : ∀ j : Fin 6,
    dir witness (71+j.val) = ([0, 1, 2, 3, 4, 2] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
theorem pair_counts : coreAlpha witness 72 = 3 ∧
    coreAlpha witness 76 = 3 := by decide +kernel
theorem attains : ∃ p : Snake 146,
    coreAlpha p 72 + coreAlpha p 76 = 6 ∧
    (∀ j : Fin 6, dir p (71+j.val) = ([0, 1, 2, 3, 4, 2] : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [pair_counts.1,pair_counts.2]

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms attains
end Snake9.ExteriorTurn.Short
