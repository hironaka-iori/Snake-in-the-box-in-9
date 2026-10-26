import LocalWindowSat.SharePressure520
import LocalWindowUnsat.SharePressure520
import Mathlib.Tactic
namespace Snake9.LocalWindow.SharePressure520
theorem refuted_share : RefutedShare window bounds resolution cap :=
  Tags.refutedShare_of_sat sat unsat
theorem positive_share (S E : Nat → Bool) (h : Axioms S E window (centresOf window bounds)) :
    96 ≤ shareSum 12 S (centresOf window bounds) := by
  by_contra! hn
  exact refuted_share S E ⟨h,by simpa [resolution,cap] using (show shareSum 12 S (centresOf window bounds) ≤ 95 by omega)⟩
#print axioms refuted_share
#print axioms positive_share
end Snake9.LocalWindow.SharePressure520
