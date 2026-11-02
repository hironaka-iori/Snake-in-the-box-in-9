import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch06
import Port95M67ChargeBatch07
import Port95M67ChargeBatch08
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_035_0 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 0, 4, 6] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G032.in_snake p P s hr hP

#print axioms word_035_0

theorem word_036_0 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 0] 7 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G034.in_snake p P s hr hP

#print axioms word_036_0

theorem word_036_1 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 6] 7 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G035.in_snake p P s hr hP

#print axioms word_036_1

theorem word_037_0 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 2, 0, 5] 6 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G033.in_snake p P s hr hP

#print axioms word_037_0

theorem word_037_1 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 2, 6, 5] 6 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G036.in_snake p P s hr hP

#print axioms word_037_1

theorem word_038_0 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 0] 14 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G037.in_snake p P s hr hP

#print axioms word_038_0

theorem word_038_1 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 6] 14 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G038.in_snake p P s hr hP

#print axioms word_038_1

theorem word_039_0 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 0] 5 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G039.in_snake p P s hr hP

#print axioms word_039_0

theorem word_039_1 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 7] 5 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G040.in_snake p P s hr hP

#print axioms word_039_1


end Snake9.ConcreteCatalogue95
