import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch08
import Port95M67ChargeBatch09
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_040_0 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 0] 5 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G041.in_snake p P s hr hP

#print axioms word_040_0

theorem word_040_1 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 7] 5 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G042.in_snake p P s hr hP

#print axioms word_040_1

theorem word_041_0 : WordShareBound [0, 1, 2, 3, 4, 5, 0, 4, 3, 1, 6] 7 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G043.in_snake p P s hr hP

#print axioms word_041_0

theorem word_042_0 : WordShareBound [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 2] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G045.in_snake p P s hr hP

#print axioms word_042_0

theorem word_043_0 : WordShareBound [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 0] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G044.in_snake p P s hr hP

#print axioms word_043_0

theorem word_043_1 : WordShareBound [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 7] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G046.in_snake p P s hr hP

#print axioms word_043_1

theorem word_044_0 : WordShareBound [0, 1, 2, 3, 4, 5, 2, 3, 6, 2, 5] 15 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G047.in_snake p P s hr hP

#print axioms word_044_0


end Snake9.ConcreteCatalogue95
