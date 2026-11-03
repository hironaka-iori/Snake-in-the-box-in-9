import CanonicalExclusions
import EndpointGeometry122
namespace Snake9.BalancedWitness133
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.EndpointGeometry122
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def values : Array Nat := #[25, 29, 31, 63, 47, 43, 41, 105, 361, 353, 289, 291, 295, 294, 302, 430, 174, 166, 230, 198, 454, 326, 322, 66, 98, 34, 32, 0, 1, 3, 7, 6, 14, 10, 26, 18, 274, 275, 283, 267, 331, 75, 79, 207, 239, 495, 511, 479, 471, 469, 468, 464, 448, 192, 224, 232, 488, 504, 505, 497, 499, 498, 434, 432, 436, 420, 484, 485, 229, 245, 253, 189, 173, 429, 301, 317, 309, 373, 372, 368, 112, 120, 122, 250, 218, 474, 346, 344, 345, 349, 333, 461, 457, 201, 137, 139, 155, 147, 151, 150, 158, 156, 140, 132, 133, 389, 261, 260, 276, 20, 52, 54, 118, 86, 94, 92, 76, 68, 69, 85, 81, 83, 115, 51, 49, 177, 161, 163, 227, 195, 451, 387, 386, 130]

def vertex (i : Fin 134) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 134, vertex i = vertex j → i = j := by decide +kernel

theorem induced : ∀ i j : Fin 134, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel

def witness : Snake 133 := ⟨vertex,distinct,induced⟩

theorem window_directions : ∀ j : Fin 6,
    dir witness (27+j.val) = ([0,1,2,0,3,2] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel

theorem canonical_window : canon (dsOf witness 27 6) = [0,1,2,0,3,2] := by
  simp only [dsOf, dir, Tags.dirOfStep_eq]
  decide +kernel

theorem pair_counts : coreAlpha witness 29 = 4 ∧ coreAlpha witness 31 = 5 := by
  decide +kernel

theorem endpoint_locations : vx witness 0 = 25 ∧ vx witness 133 = 130 ∧
    vx witness 27 = 0 ∧ vx witness 29 = 3 ∧ vx witness 31 = 6 := by decide +kernel

theorem endpoint_distances :
    hamming (vx witness 29) (vx witness 0) = 3 ∧
    hamming (vx witness 31) (vx witness 0) = 5 ∧
    hamming (vx witness 29) (vx witness 133) = 2 ∧
    hamming (vx witness 31) (vx witness 133) = 2 := by decide +kernel

theorem no_balanced_pair_floor_ten :
    ¬ (∀ (m : Nat) (p : Snake m) (r : Nat), r+6 ≤ m →
      canon (dsOf p r 6) = [0,1,2,0,3,2] →
      4 ≤ coreAlpha p (r+2) → 4 ≤ coreAlpha p (r+4) →
      10 ≤ coreAlpha p (r+2)+coreAlpha p (r+4)) := by
  intro h
  have hp := pair_counts
  have hbad := h 133 witness 27 (by decide) canonical_window
    (by simpa only [hp.1] using (show 4 ≤ 4 by omega))
    (by simpa only [hp.2] using (show 4 ≤ 5 by omega))
  norm_num at hbad
  omega

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms canonical_window
#print axioms pair_counts
#print axioms endpoint_locations
#print axioms endpoint_distances
#print axioms no_balanced_pair_floor_ten
end Snake9.BalancedWitness133
