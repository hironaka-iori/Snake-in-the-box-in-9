import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch10
import Port95M67ChargeBatch11
import Port95M67ChargeBatch12
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_050_0 : WordShareBound [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 0] 20 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G050.in_snake p P s hr hP

#print axioms word_050_0

theorem word_050_1 : WordShareBound [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 7] 20 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G054.in_snake p P s hr hP

#print axioms word_050_1

theorem word_051_0 : WordShareBound [0, 1, 2, 3, 4, 5, 3, 2, 6, 5, 3] 13 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G057.in_snake p P s hr hP

#print axioms word_051_0

theorem word_052_0 : WordShareBound [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 2] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G059.in_snake p P s hr hP

#print axioms word_052_0

theorem word_053_0 : WordShareBound [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 0] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G058.in_snake p P s hr hP

#print axioms word_053_0

theorem word_053_1 : WordShareBound [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 7] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G060.in_snake p P s hr hP

#print axioms word_053_1

theorem word_054_0 : WordShareBound [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 0] 16 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G061.in_snake p P s hr hP

#print axioms word_054_0

theorem word_054_1 : WordShareBound [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 7] 16 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G062.in_snake p P s hr hP

#print axioms word_054_1


end Snake9.ConcreteCatalogue95
