import LocalWindowBridge
import LocalWindowTags
import LocalWindowSat.C223FwdDistinct
import LocalWindowUnsat.C223FwdDistinct
import LocalWindowSat.C223FwdRepeated
import LocalWindowUnsat.C223FwdRepeated
import LocalWindowSat.C223RevDistinct
import LocalWindowUnsat.C223RevDistinct
import LocalWindowSat.C223RevRepeated
import LocalWindowUnsat.C223RevRepeated
import LocalWindowSat.C224FwdDistinct
import LocalWindowUnsat.C224FwdDistinct
import LocalWindowSat.C224FwdRepeated
import LocalWindowUnsat.C224FwdRepeated
import LocalWindowSat.C224RevDistinct
import LocalWindowUnsat.C224RevDistinct
import LocalWindowSat.C224RevRepeated
import LocalWindowUnsat.C224RevRepeated
import LocalWindowSat.C232FwdDistinct
import LocalWindowUnsat.C232FwdDistinct
import LocalWindowSat.C232FwdRepeated
import LocalWindowUnsat.C232FwdRepeated
import LocalWindowSat.C323FwdDistinct
import LocalWindowUnsat.C323FwdDistinct
import LocalWindowSat.C323FwdRepeated
import LocalWindowUnsat.C323FwdRepeated
import LocalWindowSat.C41cFwdDistinct
import LocalWindowUnsat.C41cFwdDistinct
import LocalWindowSat.C41cFwdRepeated
import LocalWindowUnsat.C41cFwdRepeated
import LocalWindowSat.C41cRevDistinct
import LocalWindowUnsat.C41cRevDistinct
import LocalWindowSat.C41cRevRepeated
import LocalWindowUnsat.C41cRevRepeated
import LocalWindowSat.C2423FwdS01203
import LocalWindowUnsat.C2423FwdS01203
import LocalWindowSat.C2423FwdS01230
import LocalWindowUnsat.C2423FwdS01230
import LocalWindowSat.C2423FwdS01234
import LocalWindowUnsat.C2423FwdS01234
import LocalWindowSat.C2423RevS01203
import LocalWindowUnsat.C2423RevS01203
import LocalWindowSat.C2423RevS01230
import LocalWindowUnsat.C2423RevS01230
import LocalWindowSat.C2423RevS01234
import LocalWindowUnsat.C2423RevS01234

/-!
# The 22 local window certificates, kernel-checked

For each certificate, `LocalWindowSat.<M>.sat` shows that every clause of its UNSAT
core follows from the snake axioms, and `LocalWindowUnsat.<M>.unsat` replays the
drat-trim LRAT refutation of that core with the verified checker `LratCheck`.
Together they give `Refuted window bounds`, and all 22 give `AllRefuted`, the only
hypothesis of `upper_242_of_refuted` and `upper_241_of_refuted`.
-/

namespace Snake9.LocalWindow

theorem allRefuted : AllRefuted := ⟨
  Tags.refuted_of_sat C223FwdDistinct.sat C223FwdDistinct.unsat,
  Tags.refuted_of_sat C223FwdRepeated.sat C223FwdRepeated.unsat,
  Tags.refuted_of_sat C223RevDistinct.sat C223RevDistinct.unsat,
  Tags.refuted_of_sat C223RevRepeated.sat C223RevRepeated.unsat,
  Tags.refuted_of_sat C224FwdDistinct.sat C224FwdDistinct.unsat,
  Tags.refuted_of_sat C224FwdRepeated.sat C224FwdRepeated.unsat,
  Tags.refuted_of_sat C224RevDistinct.sat C224RevDistinct.unsat,
  Tags.refuted_of_sat C224RevRepeated.sat C224RevRepeated.unsat,
  Tags.refuted_of_sat C232FwdDistinct.sat C232FwdDistinct.unsat,
  Tags.refuted_of_sat C232FwdRepeated.sat C232FwdRepeated.unsat,
  Tags.refuted_of_sat C323FwdDistinct.sat C323FwdDistinct.unsat,
  Tags.refuted_of_sat C323FwdRepeated.sat C323FwdRepeated.unsat,
  Tags.refuted_of_sat C41cFwdDistinct.sat C41cFwdDistinct.unsat,
  Tags.refuted_of_sat C41cFwdRepeated.sat C41cFwdRepeated.unsat,
  Tags.refuted_of_sat C41cRevDistinct.sat C41cRevDistinct.unsat,
  Tags.refuted_of_sat C41cRevRepeated.sat C41cRevRepeated.unsat,
  Tags.refuted_of_sat C2423FwdS01203.sat C2423FwdS01203.unsat,
  Tags.refuted_of_sat C2423FwdS01230.sat C2423FwdS01230.unsat,
  Tags.refuted_of_sat C2423FwdS01234.sat C2423FwdS01234.unsat,
  Tags.refuted_of_sat C2423RevS01203.sat C2423RevS01203.unsat,
  Tags.refuted_of_sat C2423RevS01230.sat C2423RevS01230.unsat,
  Tags.refuted_of_sat C2423RevS01234.sat C2423RevS01234.unsat⟩

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefuted
