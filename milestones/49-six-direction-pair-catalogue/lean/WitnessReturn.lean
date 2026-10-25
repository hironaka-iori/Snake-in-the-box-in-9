import LocalWindowTags
import LocalWindowBridge

namespace Snake9.FourStepReturn.Return
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def values : Array Nat := #[13, 12, 268, 264, 265, 267, 271, 287, 31, 27, 25, 24, 152, 144, 145, 209, 81, 83, 87, 215, 151, 407, 391, 387, 385, 449, 321, 323, 327, 326, 454, 486, 484, 480, 496, 504, 440, 441, 443, 427, 491, 495, 511, 255, 254, 238, 236, 204, 460, 456, 458, 202, 218, 210, 466, 467, 475, 347, 379, 371, 369, 373, 501, 437, 421, 429, 173, 189, 157, 221, 477, 349, 348, 92, 94, 78, 79, 75, 73, 201, 137, 139, 143, 142, 398, 414, 412, 404, 388, 132, 133, 197, 69, 68, 64, 0, 1, 3, 7, 6, 22, 20, 21, 277, 273, 272, 274, 306, 314, 58, 122, 106, 362, 366, 302, 46, 47, 43, 41, 40, 168, 160, 161, 225, 97, 99, 103, 231, 167, 166, 182, 180, 244, 116, 112, 48, 49, 51, 55, 311, 295, 291, 289, 288, 292, 36, 37]
def vertex (i : Fin 147) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem distinct : ∀ i j : Fin 147, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin 147, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake 146 := ⟨vertex, distinct, induced⟩
theorem window_directions : ∀ j : Fin 4,
    dir witness (95+j.val) = ([0, 1, 2, 0] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
theorem pair_counts : coreAlpha witness 96 = 2 ∧
    coreAlpha witness 98 = 3 := by decide +kernel
theorem attains : ∃ p : Snake 146,
    coreAlpha p 96 + coreAlpha p 98 = 5 ∧
    (∀ j : Fin 4, dir p (95+j.val) = ([0, 1, 2, 0] : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [pair_counts.1,pair_counts.2]

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms attains
end Snake9.FourStepReturn.Return
