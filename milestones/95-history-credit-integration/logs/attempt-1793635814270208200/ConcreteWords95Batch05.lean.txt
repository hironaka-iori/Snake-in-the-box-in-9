import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch03
import Port95M67ChargeBatch04
import Port95M67ChargeBatch05
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_025_0 : WordShareBound [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 6] 13 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G019.in_snake p P s hr hP

#print axioms word_025_0

theorem word_026_0 : WordShareBound [0, 1, 2, 3, 1, 4, 5, 0, 4, 1, 6] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G020.in_snake p P s hr hP

#print axioms word_026_0

theorem word_027_0 : WordShareBound [0, 1, 2, 3, 1, 4, 5, 1, 3, 2, 1] 5 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G022.in_snake p P s hr hP

#print axioms word_027_0

theorem word_028_0 : WordShareBound [0, 1, 2, 3, 1, 4, 5, 1, 3, 0, 1] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G021.in_snake p P s hr hP

#print axioms word_028_0

theorem word_028_1 : WordShareBound [0, 1, 2, 3, 1, 4, 5, 1, 3, 6, 1] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G023.in_snake p P s hr hP

#print axioms word_028_1

theorem word_029_0 : WordShareBound [0, 1, 2, 3, 1, 4, 5, 6, 4, 1, 0] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G024.in_snake p P s hr hP

#print axioms word_029_0

theorem word_029_1 : WordShareBound [0, 1, 2, 3, 1, 4, 5, 6, 4, 1, 7] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G025.in_snake p P s hr hP

#print axioms word_029_1


end Snake9.ConcreteCatalogue95
