import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch00
import Port95M67ChargeBatch01
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_010_0 : WordShareBound [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 1] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G002.in_snake p P s hr hP

#print axioms word_010_0

theorem word_010_1 : WordShareBound [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 6] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G003.in_snake p P s hr hP

#print axioms word_010_1

theorem word_011_0 : WordShareBound [0, 1, 2, 0, 3, 2, 4, 5, 6, 4, 2] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G004.in_snake p P s hr hP

#print axioms word_011_0

theorem word_012_0 : WordShareBound [0, 1, 2, 0, 3, 4, 0, 2, 5, 1, 0] 20 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G007.in_snake p P s hr hP

#print axioms word_012_0

theorem word_013_0 : WordShareBound [0, 1, 2, 0, 3, 4, 0, 2, 5, 0, 1] 6 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G005.in_snake p P s hr hP

#print axioms word_013_0

theorem word_013_1 : WordShareBound [0, 1, 2, 0, 3, 4, 0, 2, 5, 0, 6] 6 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G006.in_snake p P s hr hP

#print axioms word_013_1

theorem word_014_0 : WordShareBound [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 2] 9 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G008.in_snake p P s hr hP

#print axioms word_014_0


end Snake9.ConcreteCatalogue95
