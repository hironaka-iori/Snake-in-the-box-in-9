import LocalWindowTags
import LocalWindowBridge
import Mathlib.Tactic
namespace Snake9.TripleReturn
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def values : Array Nat := #[10, 138, 139, 137, 141, 157, 189, 191, 175, 174, 46, 302, 303, 319, 311, 55, 54, 118, 86, 87, 343, 351, 335, 334, 78, 206, 207, 223, 219, 91, 75, 73, 72, 200, 232, 234, 250, 254, 252, 220, 92, 93, 125, 127, 111, 103, 99, 97, 96, 100, 68, 69, 197, 193, 195, 194, 210, 208, 80, 81, 337, 321, 320, 256, 0, 1, 3, 7, 15, 31, 30, 286, 284, 316, 308, 436, 420, 388, 396, 398, 399, 415, 411, 283, 267, 265, 269, 261, 277, 21, 20, 148, 150, 151, 147, 145, 401, 385, 387, 386, 402, 434, 442, 314, 58, 59, 43, 41, 45, 37, 165, 161, 160, 176, 48, 49, 305, 289, 291, 290, 354, 362, 360, 364, 492, 493, 489, 505, 249, 241, 243, 499, 503, 487, 486, 454, 470, 478, 474, 472, 408, 152, 24, 25]
def vertex (i : Fin 144) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem distinct : ∀ i j : Fin 144, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin 144, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake 143 := ⟨vertex, distinct, induced⟩
theorem window_directions : ∀ j : Fin 6,
    dir witness (64+j.val) = ([0,1,2,3,4,0] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
theorem triple_counts : coreAlpha witness 65 = 3 ∧
    coreAlpha witness 68 = 5 ∧ coreAlpha witness 69 = 5 := by decide +kernel

theorem attains : ∃ p : Snake 143,
    coreAlpha p 65 + coreAlpha p 68 + coreAlpha p 69 = 13 ∧
    (∀ j : Fin 6, dir p (64+j.val) = ([0,1,2,3,4,0] : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [triple_counts.1,triple_counts.2.1,triple_counts.2.2]

theorem sharp_constant (K : Nat)
    (h : ∀ {m : Nat} (p : Snake m) (r : Nat), r+6 ≤ m →
      (∀ j, j<6 → dir p (r+j) = ([0,1,2,3,4,0] : List Nat).getD j 0) →
      K ≤ coreAlpha p (r+1)+coreAlpha p (r+4)+coreAlpha p (r+5)) : K ≤ 13 := by
  have hb := h witness 64 (by decide)
    (by intro j hj; exact window_directions ⟨j,hj⟩)
  norm_num only at hb
  rw [triple_counts.1,triple_counts.2.1,triple_counts.2.2] at hb
  exact hb
#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms triple_counts
#print axioms attains
#print axioms sharp_constant
end Snake9.TripleReturn
