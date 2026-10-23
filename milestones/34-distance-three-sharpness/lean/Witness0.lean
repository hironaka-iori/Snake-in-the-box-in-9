import LocalWindowTags
import LocalWindowBridge

namespace Snake9.PairSharpness.Case0
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def values : Array Nat := #[193, 195, 211, 210, 82, 338, 339, 323, 321, 325, 69, 85, 81, 89, 73, 75, 74, 202, 138, 394, 266, 258, 262, 326, 454, 198, 196, 132, 148, 149, 145, 153, 137, 141, 205, 221, 220, 216, 472, 456, 457, 459, 491, 427, 299, 291, 289, 288, 292, 36, 52, 53, 49, 57, 41, 45, 109, 125, 124, 126, 118, 102, 103, 99, 97, 96, 64, 0, 1, 3, 7, 15, 31, 29, 28, 24, 26, 58, 186, 187, 251, 123, 379, 377, 376, 312, 316, 317, 319, 311, 279, 277, 273, 281, 265, 269, 268, 396, 412, 413, 415, 411, 403, 387, 385, 384, 400, 432, 176, 240, 244, 500, 372, 340, 348, 349, 351, 335, 367, 366, 302, 430, 446, 510, 506, 498, 499, 503, 247, 183, 182, 166, 162, 163, 161, 165, 229, 485, 493, 492, 236, 172, 188, 189]
def vertex (i : Fin 144) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 144, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin 144, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake 143 := ⟨vertex, distinct, induced⟩

theorem window_directions : ∀ j : Fin 7,
    dir witness (67+j.val) = ([0, 1, 2, 3, 4, 1, 0] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel

theorem pair_counts : coreAlpha witness 68 = 6 ∧
    coreAlpha witness 73 = 4 := by decide +kernel

theorem attains : ∃ p : Snake 143,
    coreAlpha p 68 + coreAlpha p 73 = 10 ∧
    (∀ j : Fin 7, dir p (67+j.val) = ([0, 1, 2, 3, 4, 1, 0] : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [pair_counts.1,pair_counts.2]

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms attains
end Snake9.PairSharpness.Case0
