import IntervalGuards

namespace Snake9.ShortRules81
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.GraphWalk78 Snake9.CountGeometry78
set_option maxHeartbeats 2000000

def orientedPosition (L : Nat) (reverse : Bool) (j : Nat) : Nat :=
  if reverse then L-j else j

def orientedSnake {m : Nat} (p : Snake m) (reverse : Bool) : Snake m :=
  if reverse then revSnake p else p

def orientedStart (m r offset L : Nat) (reverse : Bool) : Nat :=
  if reverse then m-(r+offset)-L else r+offset

theorem oriented_window_fits {m : Nat} (p : Snake m) (r offset L : Nat)
    (reverse : Bool) (hr : r+9 ≤ m) (ho : offset+L ≤ 9) :
    orientedStart m r offset L reverse + L ≤ m := by
  cases reverse <;> simp only [orientedStart, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem oriented_count {m : Nat} (p : Snake m) (r offset L j : Nat)
    (reverse : Bool) (hr : r+9 ≤ m) (ho : offset+L ≤ 9) (hj : j ≤ L) :
    coreAlpha (orientedSnake p reverse) (orientedStart m r offset L reverse+j) =
      coreAlpha p (r+offset+orientedPosition L reverse j) := by
  cases reverse
  · rfl
  · simp only [orientedSnake, orientedStart, orientedPosition, ↓reduceIte]
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega

theorem encoded_oriented_count {m : Nat} (p : Snake m) (r offset L j : Nat)
    (reverse : Bool) (hr : r+9 ≤ m) (ho : offset+L ≤ 9) (hj : j ≤ L)
    (hpos : 3 ≤ offset+orientedPosition L reverse j ∧
      offset+orientedPosition L reverse j ≤ 8) :
    digit (sixCode p r) (offset+orientedPosition L reverse j-3) =
      min 6 (coreAlpha (orientedSnake p reverse)
        (orientedStart m r offset L reverse+j)) := by
  rw [actual_digit p r _ hr (by omega), oriented_count p r offset L j reverse hr ho hj]
  unfold truncatedCount
  congr 2
  omega

theorem oriented_shape {m : Nat} (p : Snake m) (r offset L : Nat)
    (reverse : Bool) (hr : r+9 ≤ m) (ho : offset+L ≤ 9) :
    canon (dsOf (orientedSnake p reverse) (orientedStart m r offset L reverse) L) =
      canon (if reverse then (((canon (dsOf p r 9)).drop offset).take L).reverse
        else ((canon (dsOf p r 9)).drop offset).take L) := by
  cases reverse
  · simp only [orientedSnake, orientedStart, ↓reduceIte]
    exact (canonical_nine_slice p r offset L hr ho).symm
  · simp only [orientedSnake, orientedStart, ↓reduceIte]
    rw [dsOf_rev p (r+offset) L (by omega)]
    exact (canonical_nine_slice_reverse p r offset L hr ho).symm

theorem canonical_permutation {m : Nat} (p : Snake m) (r L : Nat)
    (hr : r+L ≤ m) :
    ∃ P : CPerm, ∀ j, j < L →
      P.fwd (dir p (r+j)) = (canon (dsOf p r L)).getD j 0 := by
  obtain ⟨u,hu,hu9,hlen,hcs⟩ := actual_canonical_frame p r L hr
  refine ⟨mkPerm u, ?_⟩
  intro j hj
  obtain ⟨hi,hd⟩ := hcs j hj
  rw [← hd]
  exact mkPerm_spec hu hu9 hlen _ hi

#print axioms oriented_window_fits
#print axioms oriented_count
#print axioms encoded_oriented_count
#print axioms oriented_shape
#print axioms canonical_permutation
end Snake9.ShortRules81
