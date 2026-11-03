import LocalWindowTags
import LocalWindowBridge
import ReferenceInterface

namespace Snake9.Boundary121.Pair26
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def values : Array Nat := #[66, 322, 323, 327, 335, 79, 75, 73, 72, 76, 68, 84, 86, 87, 83, 81, 337, 341, 469, 501, 497, 499, 435, 443, 315, 314, 318, 446, 190, 188, 156, 140, 132, 133, 389, 421, 417, 161, 163, 167, 166, 422, 486, 494, 462, 206, 198, 199, 195, 193, 449, 448, 480, 224, 96, 97, 99, 103, 102, 110, 126, 124, 125, 93, 221, 205, 461, 493, 365, 357, 356, 372, 374, 375, 383, 511, 255, 239, 235, 234, 250, 218, 474, 346, 344, 348, 476, 508, 504, 440, 432, 304, 305, 49, 51, 55, 54, 52, 36, 44, 300, 268, 260, 276, 404, 406, 150, 151, 147, 145, 153, 25, 27, 31, 287, 279, 275, 274, 18, 16, 0, 1, 3, 7, 6, 14, 10, 138, 130, 386, 387, 395, 267, 265, 297, 41, 43, 47, 303, 295, 291, 290, 34]
private def vertex (i : Fin 143) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 143, vertex i = vertex j → i = j := by
  decide +kernel
#print axioms distinct

theorem induced : ∀ i j : Fin 143, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by
  decide +kernel
#print axioms induced

def witness : Snake 142 := ⟨vertex, distinct, induced⟩

theorem window_directions : ∀ j : Fin 6,
    dir witness (120+j.val) = ([0,1,2,0,3,2] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_directions

theorem window_word : dsOf witness 120 6 = [0,1,2,0,3,2] := by
  simp only [dsOf, dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_word

theorem canonical_window : canon (dsOf witness 120 6) = [0,1,2,0,3,2] := by
  rw [window_word]
  rfl
#print axioms canonical_window

theorem counts : coreAlpha witness 122 = 2 ∧
    coreAlpha witness 124 = 6 := by
  decide +kernel
#print axioms counts

theorem total : coreAlpha witness 122 + coreAlpha witness 124 = 8 := by
  rcases counts with ⟨h2,h4⟩
  omega
#print axioms total

theorem attainment : ∃ p : Snake 142,
    120+6 ≤ 142 ∧ canon (dsOf p 120 6) = [0,1,2,0,3,2] ∧
    coreAlpha p 122 = 2 ∧ coreAlpha p 124 = 6 ∧
    coreAlpha p 122 + coreAlpha p 124 = 8 := by
  exact ⟨witness,by decide,canonical_window,counts.1,counts.2,total⟩
#print axioms attainment
end Snake9.Boundary121.Pair26
