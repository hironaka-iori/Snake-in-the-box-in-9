import SumWindow441
import WitnessSharp
import WitnessShort

namespace Snake9.ExteriorTurn
open Snake9.LocalWindow
theorem sharp_constant (K : Nat)
    (h : ∀ {m : Nat} (p : Snake m) (r : Nat), r+8 ≤ m →
      (∀ j, j<8 → dir p (r+j) = ([0,1,2,3,4,0,3,1] : List Nat).getD j 0) →
      K ≤ coreAlpha p (r+2)+coreAlpha p (r+6)) : K ≤ 7 := by
  have hb := h Sharp.witness 2 (by decide)
    (by intro j hj; exact Sharp.window_directions ⟨j,hj⟩)
  norm_num only at hb
  rw [Sharp.pair_counts.1,Sharp.pair_counts.2] at hb
  exact hb

theorem shorter_claim_false : ¬ (∀ {m : Nat} (p : Snake m) (r : Nat), r+6 ≤ m →
    (∀ j, j<6 → dir p (r+j) = ([0,1,2,3,4,2] : List Nat).getD j 0) →
    7 ≤ coreAlpha p (r+1)+coreAlpha p (r+5)) := by
  intro h
  have hb := h Short.witness 71 (by decide)
    (by intro j hj; exact Short.window_directions ⟨j,hj⟩)
  norm_num only at hb
  rw [Short.pair_counts.1,Short.pair_counts.2] at hb
  omega

#print axioms sharp_constant
#print axioms shorter_claim_false
end Snake9.ExteriorTurn
