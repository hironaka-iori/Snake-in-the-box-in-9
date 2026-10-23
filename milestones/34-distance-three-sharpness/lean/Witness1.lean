import LocalWindowTags
import LocalWindowBridge

namespace Snake9.PairSharpness.Case1
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def values : Array Nat := #[77, 73, 89, 81, 85, 87, 215, 223, 221, 253, 249, 251, 507, 443, 315, 314, 306, 434, 498, 496, 368, 336, 344, 472, 476, 468, 470, 454, 390, 422, 166, 182, 180, 188, 156, 158, 142, 206, 238, 239, 231, 487, 503, 375, 311, 295, 291, 289, 288, 416, 384, 385, 387, 403, 407, 415, 413, 397, 141, 133, 149, 145, 153, 155, 139, 203, 195, 193, 192, 64, 0, 1, 3, 7, 15, 31, 29, 61, 317, 381, 349, 351, 347, 339, 323, 321, 325, 261, 277, 273, 281, 265, 267, 266, 394, 426, 490, 362, 360, 361, 489, 493, 492, 484, 356, 358, 102, 118, 116, 124, 92, 94, 90, 26, 24, 56, 48, 49, 51, 179, 163, 161, 169, 41, 43, 107, 99, 97, 101, 37, 36, 44, 12, 268, 284, 286, 278, 22, 20]
def vertex (i : Fin 139) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 139, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin 139, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake 138 := ⟨vertex, distinct, induced⟩

theorem window_directions : ∀ j : Fin 7,
    dir witness (70+j.val) = ([0, 1, 2, 3, 4, 1, 5] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel

theorem pair_counts : coreAlpha witness 71 = 5 ∧
    coreAlpha witness 76 = 4 := by decide +kernel

theorem attains : ∃ p : Snake 138,
    coreAlpha p 71 + coreAlpha p 76 = 9 ∧
    (∀ j : Fin 7, dir p (70+j.val) = ([0, 1, 2, 3, 4, 1, 5] : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [pair_counts.1,pair_counts.2]

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms attains
end Snake9.PairSharpness.Case1
