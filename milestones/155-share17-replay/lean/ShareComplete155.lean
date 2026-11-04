import CriticalShareAdapter154
import ReplayUnsat153

namespace Snake9.CriticalShare155
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

theorem share17
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hcase :
      (canon (dsOf p r 6) = [0,1,2,0,3,2] ∧
        coreAlpha p (r+1) = 4 ∧ coreAlpha p (r+2) ≤ 4 ∧
        coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 5 ∧
        coreAlpha p (r+5) = 3) ∨
      (canon (dsOf p r 6).reverse = [0,1,2,0,3,2] ∧
        coreAlpha p (r+1) = 3 ∧ coreAlpha p (r+2) ≤ 5 ∧
        coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 4 ∧
        coreAlpha p (r+5) = 4)) :
    17 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum :=
  Snake9.CriticalShare154.share17_of_core_unsat Snake9.ReplayFull153.unsat p r hr hcase

#print axioms share17
end Snake9.CriticalShare155
