import LocalWindowSat.SharePressure513
import LocalWindowUnsat.SharePressure513
import Mathlib.Tactic
namespace Snake9.LocalWindow.SharePressure513
theorem refuted_share : RefutedShare window bounds resolution cap :=
  Tags.refutedShare_of_sat sat unsat
theorem positive_share (S E : Nat → Bool) (h : Axioms S E window (centresOf window bounds)) :
    48 ≤ shareSum 12 S (centresOf window bounds) := by
  by_contra! hn
  exact refuted_share S E ⟨h,by simpa [resolution,cap] using (show shareSum 12 S (centresOf window bounds) ≤ 47 by omega)⟩
#print axioms refuted_share
#print axioms positive_share
end Snake9.LocalWindow.SharePressure513
