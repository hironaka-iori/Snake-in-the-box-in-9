import Witness0
import Witness1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Snake9.PairSharpness
open Snake9.LocalWindow

theorem first_constant_cannot_increase :
    ¬ (∀ (m : Nat) (p : Snake m) (r : Nat), r+7 ≤ m →
      (∀ j : Fin 7, dir p (r+j.val) = ([0,1,2,3,4,1,0] : List Nat).getD j.val 0) →
      11 ≤ coreAlpha p (r+1) + coreAlpha p (r+6)) := by
  intro h
  have hc := h 143 Case0.witness 67 (by decide) Case0.window_directions
  change 11 ≤ coreAlpha Case0.witness 68 + coreAlpha Case0.witness 73 at hc
  rw [Case0.pair_counts.1,Case0.pair_counts.2] at hc
  omega

theorem second_constant_cannot_increase :
    ¬ (∀ (m : Nat) (p : Snake m) (r : Nat), r+7 ≤ m →
      (∀ j : Fin 7, dir p (r+j.val) = ([0,1,2,3,4,1,5] : List Nat).getD j.val 0) →
      10 ≤ coreAlpha p (r+1) + coreAlpha p (r+6)) := by
  intro h
  have hc := h 138 Case1.witness 70 (by decide) Case1.window_directions
  change 10 ≤ coreAlpha Case1.witness 71 + coreAlpha Case1.witness 76 at hc
  rw [Case1.pair_counts.1,Case1.pair_counts.2] at hc
  omega

#print axioms first_constant_cannot_increase
#print axioms second_constant_cannot_increase
end Snake9.PairSharpness
