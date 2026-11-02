import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch09
import Port95M67ChargeBatch10
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_045_0 : WordShareBound [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 6] 10 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G048.in_snake p P s hr hP

#print axioms word_045_0

theorem word_046_0 : WordShareBound [0, 1, 2, 3, 4, 5, 3, 2, 0, 4, 6] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G049.in_snake p P s hr hP

#print axioms word_046_0

theorem word_047_0 : WordShareBound [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 3] 20 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G051.in_snake p P s hr hP

#print axioms word_047_0

theorem word_048_0 : WordShareBound [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 4] 10 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G052.in_snake p P s hr hP

#print axioms word_048_0

theorem word_049_0 : WordShareBound [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 5] 10 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G053.in_snake p P s hr hP

#print axioms word_049_0


end Snake9.ConcreteCatalogue95
