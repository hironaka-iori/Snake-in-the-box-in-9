import CanonicalExclusions
import EndpointGeometry122
namespace Snake9.Witness133
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.EndpointGeometry122
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def values : Array Nat := #[18, 50, 54, 62, 63, 31, 27, 25, 153, 145, 147, 151, 150, 158, 156, 188, 444, 440, 432, 400, 464, 472, 476, 348, 92, 94, 86, 87, 83, 81, 337, 321, 323, 355, 99, 98, 102, 110, 111, 79, 75, 73, 201, 193, 195, 199, 198, 206, 204, 236, 492, 488, 480, 352, 368, 372, 500, 244, 246, 247, 243, 499, 497, 505, 509, 511, 510, 506, 250, 218, 219, 223, 221, 213, 469, 405, 437, 181, 53, 21, 20, 276, 278, 279, 275, 307, 315, 443, 411, 410, 282, 346, 330, 334, 326, 324, 68, 69, 101, 229, 485, 487, 423, 419, 387, 385, 393, 265, 267, 271, 303, 301, 365, 333, 461, 463, 459, 491, 235, 171, 43, 41, 40, 44, 36, 292, 294, 290, 258, 256, 0, 1, 3, 7, 6, 14, 10, 138, 130, 162, 166, 174, 430, 398, 390, 388, 132, 133, 141, 13]

def vertex (i : Fin 150) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 150, vertex i = vertex j → i = j := by decide +kernel

theorem induced : ∀ i j : Fin 150, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel

def witness : Snake 149 := ⟨vertex,distinct,induced⟩

theorem window_directions : ∀ j : Fin 6,
    dir witness (130+j.val) = ([0,1,2,0,3,2] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel

theorem canonical_window : canon (dsOf witness 130 6) = [0,1,2,0,3,2] := by
  simp only [dsOf, dir, Tags.dirOfStep_eq]
  decide +kernel

theorem pair_counts : coreAlpha witness 132 = 6 ∧ coreAlpha witness 134 = 3 := by
  decide +kernel

theorem endpoint_locations : vx witness 0 = 18 ∧ vx witness 149 = 13 ∧
    vx witness 130 = 0 ∧ vx witness 132 = 3 ∧ vx witness 134 = 6 := by decide +kernel

theorem endpoint_distances :
    hamming (vx witness 132) (vx witness 0) = 2 ∧
    hamming (vx witness 134) (vx witness 0) = 2 ∧
    hamming (vx witness 132) (vx witness 149) = 3 ∧
    hamming (vx witness 134) (vx witness 149) = 3 := by decide +kernel

theorem no_uniform_pair_floor_ten :
    ¬ (∀ (m : Nat) (p : Snake m) (r : Nat), r+6 ≤ m →
      canon (dsOf p r 6) = [0,1,2,0,3,2] →
      10 ≤ coreAlpha p (r+2)+coreAlpha p (r+4)) := by
  intro h
  have hbad := h 149 witness 130 (by decide) canonical_window
  have hp := pair_counts
  norm_num at hbad
  omega

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms canonical_window
#print axioms pair_counts
#print axioms endpoint_locations
#print axioms endpoint_distances
#print axioms no_uniform_pair_floor_ten
end Snake9.Witness133
