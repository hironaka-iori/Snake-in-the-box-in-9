import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch05
import Port95M67ChargeBatch06
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_030_0 : WordShareBound [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 2] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G026.in_snake p P s hr hP

#print axioms word_030_0

theorem word_031_0 : WordShareBound [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 6] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G027.in_snake p P s hr hP

#print axioms word_031_0

theorem word_032_0 : WordShareBound [0, 1, 2, 3, 4, 0, 5, 4, 3, 1, 6] 7 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G028.in_snake p P s hr hP

#print axioms word_032_0

theorem word_033_0 : WordShareBound [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 0] 16 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G029.in_snake p P s hr hP

#print axioms word_033_0

theorem word_033_1 : WordShareBound [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 6] 16 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G030.in_snake p P s hr hP

#print axioms word_033_1

theorem word_034_0 : WordShareBound [0, 1, 2, 3, 4, 1, 2, 5, 6, 2, 1] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G031.in_snake p P s hr hP

#print axioms word_034_0


end Snake9.ConcreteCatalogue95
