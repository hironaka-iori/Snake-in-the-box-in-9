import LocalWindowTags
import LocalWindowBridge
import ReferenceInterface

namespace Snake9.Boundary121.Pair44
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def values : Array Nat := #[34, 162, 163, 167, 175, 431, 430, 302, 294, 292, 36, 44, 172, 168, 232, 488, 360, 296, 312, 314, 442, 410, 474, 346, 344, 345, 349, 341, 469, 471, 479, 463, 461, 460, 476, 412, 413, 445, 317, 301, 269, 265, 267, 283, 27, 25, 57, 41, 43, 107, 99, 103, 102, 110, 238, 206, 198, 199, 195, 203, 139, 137, 141, 133, 132, 388, 390, 391, 387, 385, 449, 448, 192, 208, 209, 145, 147, 146, 150, 158, 190, 62, 54, 55, 51, 307, 291, 289, 353, 357, 485, 229, 245, 181, 180, 176, 432, 433, 497, 505, 507, 251, 243, 242, 114, 112, 368, 372, 500, 502, 510, 382, 383, 127, 125, 109, 77, 69, 68, 324, 326, 327, 323, 339, 83, 87, 86, 94, 92, 28, 20, 276, 278, 274, 258, 256, 0, 1, 3, 7, 6, 14, 10, 74, 66]
private def vertex (i : Fin 145) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 145, vertex i = vertex j → i = j := by
  decide +kernel
#print axioms distinct

theorem induced : ∀ i j : Fin 145, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by
  decide +kernel
#print axioms induced

def witness : Snake 144 := ⟨vertex, distinct, induced⟩

theorem window_directions : ∀ j : Fin 6,
    dir witness (136+j.val) = ([0,1,2,0,3,2] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_directions

theorem window_word : dsOf witness 136 6 = [0,1,2,0,3,2] := by
  simp only [dsOf, dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_word

theorem canonical_window : canon (dsOf witness 136 6) = [0,1,2,0,3,2] := by
  rw [window_word]
  rfl
#print axioms canonical_window

theorem counts : coreAlpha witness 138 = 4 ∧
    coreAlpha witness 140 = 4 := by
  decide +kernel
#print axioms counts

theorem total : coreAlpha witness 138 + coreAlpha witness 140 = 8 := by
  rcases counts with ⟨h2,h4⟩
  omega
#print axioms total

theorem attainment : ∃ p : Snake 144,
    136+6 ≤ 144 ∧ canon (dsOf p 136 6) = [0,1,2,0,3,2] ∧
    coreAlpha p 138 = 4 ∧ coreAlpha p 140 = 4 ∧
    coreAlpha p 138 + coreAlpha p 140 = 8 := by
  exact ⟨witness,by decide,canonical_window,counts.1,counts.2,total⟩
#print axioms attainment
end Snake9.Boundary121.Pair44
