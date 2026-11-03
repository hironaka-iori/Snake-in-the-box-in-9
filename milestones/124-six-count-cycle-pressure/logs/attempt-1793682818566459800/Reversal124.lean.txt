import ActualTotal124
import ReferenceInterface

namespace Snake9.Reversal124
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow Snake9.Guards79
set_option maxHeartbeats 2000000

theorem actual_reverse {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7).reverse = [0,1,2,3,0,4,1]) :
    25 ≤ coreAlpha p (r+1)+coreAlpha p (r+2)+coreAlpha p (r+3)+
      coreAlpha p (r+4)+coreAlpha p (r+5)+coreAlpha p (r+6) := by
  have hs : canon (dsOf (revSnake p) (m-r-7) 7) = [0,1,2,3,0,4,1] := by
    rw [dsOf_rev p r 7 hr]
    exact hshape
  have h := ActualTotal124.actual_total_sum (revSnake p) (m-r-7) (by omega) hs
  have h1 : coreAlpha (revSnake p) (m-r-7+1) = coreAlpha p (r+6) := by
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega
  have h2 : coreAlpha (revSnake p) (m-r-7+2) = coreAlpha p (r+5) := by
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega
  have h3 : coreAlpha (revSnake p) (m-r-7+3) = coreAlpha p (r+4) := by
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega
  have h4 : coreAlpha (revSnake p) (m-r-7+4) = coreAlpha p (r+3) := by
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega
  have h5 : coreAlpha (revSnake p) (m-r-7+5) = coreAlpha p (r+2) := by
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega
  have h6 : coreAlpha (revSnake p) (m-r-7+6) = coreAlpha p (r+1) := by
    rw [coreAlpha_rev p (by omega)]
    congr 1
    omega
  rw [h1,h2,h3,h4,h5,h6] at h
  omega

theorem actual_either {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+7 ≤ m)
    (hshape : canon (dsOf p r 7) = [0,1,2,3,0,4,1] ∨
      canon (dsOf p r 7).reverse = [0,1,2,3,0,4,1]) :
    25 ≤ coreAlpha p (r+1)+coreAlpha p (r+2)+coreAlpha p (r+3)+
      coreAlpha p (r+4)+coreAlpha p (r+5)+coreAlpha p (r+6) := by
  rcases hshape with hf | hb
  · exact ActualTotal124.actual_total_sum p r hr hf
  · exact actual_reverse p r hr hb

#print axioms actual_reverse
#print axioms actual_either
end Snake9.Reversal124
