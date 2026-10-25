import SumWindow4934
import WitnessReturn
namespace Snake9.FourStepReturn
open Snake9.LocalWindow

theorem sharp_constant (K : Nat)
    (h : ∀ {m : Nat} (p : Snake m) (r : Nat), r+4 ≤ m →
      (∀ j, j<4 → dir p (r+j) = ([0,1,2,0] : List Nat).getD j 0) →
      K ≤ coreAlpha p (r+1)+coreAlpha p (r+3)) : K ≤ 5 := by
  have hb := h Return.witness 95 (by decide)
    (by intro j hj; exact Return.window_directions ⟨j,hj⟩)
  norm_num only at hb
  rw [Return.pair_counts.1,Return.pair_counts.2] at hb
  exact hb
#print axioms sharp_constant
end Snake9.FourStepReturn
