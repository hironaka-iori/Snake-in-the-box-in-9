import LocalWindowTags
import LocalWindowBridge
import ReferenceInterface

namespace Snake9.Boundary121.Pair35
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def values : Array Nat := #[18, 274, 275, 273, 305, 304, 312, 440, 444, 428, 430, 426, 394, 392, 264, 265, 267, 271, 303, 319, 317, 285, 413, 409, 411, 475, 219, 218, 90, 94, 86, 87, 83, 81, 209, 145, 147, 179, 51, 55, 54, 62, 60, 44, 36, 100, 68, 76, 72, 73, 75, 79, 111, 109, 125, 117, 373, 372, 500, 484, 480, 488, 232, 236, 252, 220, 476, 472, 464, 336, 320, 321, 323, 327, 326, 358, 294, 290, 291, 419, 387, 391, 390, 388, 260, 276, 20, 148, 150, 158, 159, 31, 27, 25, 57, 185, 249, 505, 509, 511, 510, 506, 498, 434, 438, 439, 437, 421, 165, 167, 166, 162, 130, 128, 0, 1, 3, 7, 6, 14, 10, 42, 43, 171, 139, 137, 141, 205, 461, 463, 462, 206, 198, 199, 195, 227, 99, 98, 66]
private def vertex (i : Fin 139) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 139, vertex i = vertex j → i = j := by
  decide +kernel
#print axioms distinct

theorem induced : ∀ i j : Fin 139, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by
  decide +kernel
#print axioms induced

def witness : Snake 138 := ⟨vertex, distinct, induced⟩

theorem window_directions : ∀ j : Fin 6,
    dir witness (114+j.val) = ([0,1,2,0,3,2] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_directions

theorem window_word : dsOf witness 114 6 = [0,1,2,0,3,2] := by
  simp only [dsOf, dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_word

theorem canonical_window : canon (dsOf witness 114 6) = [0,1,2,0,3,2] := by
  rw [window_word]
  rfl
#print axioms canonical_window

theorem counts : coreAlpha witness 116 = 3 ∧
    coreAlpha witness 118 = 5 := by
  decide +kernel
#print axioms counts

theorem total : coreAlpha witness 116 + coreAlpha witness 118 = 8 := by
  rcases counts with ⟨h2,h4⟩
  omega
#print axioms total

theorem attainment : ∃ p : Snake 138,
    114+6 ≤ 138 ∧ canon (dsOf p 114 6) = [0,1,2,0,3,2] ∧
    coreAlpha p 116 = 3 ∧ coreAlpha p 118 = 5 ∧
    coreAlpha p 116 + coreAlpha p 118 = 8 := by
  exact ⟨witness,by decide,canonical_window,counts.1,counts.2,total⟩
#print axioms attainment
end Snake9.Boundary121.Pair35
