import Std

namespace Entry87.Arms

/-- An induced word in a graph with forbidden pair relation "distance < 2". -/
def Induced (n : Nat) (d : Nat → Nat → Nat) : Prop :=
  (∀ i, i+1 < n → d i (i+1) = 1) ∧
  (∀ i j, j < n → i+1 < j → 2 ≤ d i j)

/-- Three consecutive isometric pieces may be glued iff all cross-piece
nonedges pass. Index ranges deliberately overlap at the two hinges. -/
theorem glue (n a b : Nat) (d : Nat → Nat → Nat)
    (edges : ∀ i, i+1 < n → d i (i+1) = 1)
    (left : ∀ i j, j ≤ a → i+1 < j → 2 ≤ d i j)
    (middle : ∀ i j, a ≤ i → j ≤ b → i+1 < j → 2 ≤ d i j)
    (right : ∀ i j, b ≤ i → j < n → i+1 < j → 2 ≤ d i j)
    (leftMiddle : ∀ i j, i < a → a < j → j ≤ b → i+1 < j → 2 ≤ d i j)
    (middleRight : ∀ i j, a ≤ i → i < b → b < j → j < n → i+1 < j → 2 ≤ d i j)
    (outer : ∀ i j, i < a → b < j → j < n → 2 ≤ d i j) : Induced n d := by
  refine ⟨edges, ?_⟩
  intro i j hj gap
  by_cases jl : j ≤ a
  · exact left i j jl gap
  by_cases br : b ≤ i
  · exact right i j br hj gap
  by_cases il : i < a
  · by_cases jm : j ≤ b
    · exact leftMiddle i j il (by omega) jm gap
    · exact outer i j il (by omega) hj
  · by_cases jm : j ≤ b
    · exact middle i j (by omega) jm gap
    · exact middleRight i j (by omega) (by omega) (by omega) hj gap

theorem outer_necessary (n a b : Nat) (hab : a < b) (d : Nat → Nat → Nat)
    (h : Induced n d) (i j : Nat) (hil : i<a) (hjr : b<j) (hj : j<n) :
    2 ≤ d i j := h.2 i j hj (by omega)

/- Any two arms of a fixed total size can be searched left first and right
second, as both are prefixes of the same eventual induced path. -/
theorem restriction {n : Nat} {d : Nat → Nat → Nat} (h : Induced n d)
    (first length : Nat) (fits : first+length ≤ n) :
    Induced length (fun i j => d (first+i) (first+j)) := by
  constructor
  · intro i hi
    exact h.1 (first+i) (by omega)
  · intro i j hj gap
    exact h.2 (first+i) (first+j) (by omega) (by omega)

#print axioms glue
#print axioms outer_necessary
#print axioms restriction
end Entry87.Arms
