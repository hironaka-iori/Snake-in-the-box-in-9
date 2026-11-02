import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch01
import Port95M67ChargeBatch02
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_015_0 : WordShareBound [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 6] 9 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G009.in_snake p P s hr hP

#print axioms word_015_0

theorem word_016_0 : WordShareBound [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 2] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G010.in_snake p P s hr hP

#print axioms word_016_0

theorem word_017_0 : WordShareBound [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 3] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G011.in_snake p P s hr hP

#print axioms word_017_0

theorem word_018_0 : WordShareBound [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 6] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G012.in_snake p P s hr hP

#print axioms word_018_0

theorem word_019_0 : WordShareBound [0, 1, 2, 3, 0, 4, 3, 2, 5, 1, 2] 13 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G013.in_snake p P s hr hP

#print axioms word_019_0


end Snake9.ConcreteCatalogue95
