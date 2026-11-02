import CreditTransport95
import HistoryCreditEvaluator95
import Port95M67ChargeBatch02
import Port95M67ChargeBatch03
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_020_0 : WordShareBound [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 2] 8 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G015.in_snake p P s hr hP

#print axioms word_020_0

theorem word_021_0 : WordShareBound [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 0] 16 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G014.in_snake p P s hr hP

#print axioms word_021_0

theorem word_022_0 : WordShareBound [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 4] 12 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G016.in_snake p P s hr hP

#print axioms word_022_0

theorem word_023_0 : WordShareBound [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 6] 16 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G017.in_snake p P s hr hP

#print axioms word_023_0

theorem word_024_0 : WordShareBound [0, 1, 2, 3, 1, 0, 4, 2, 5, 3, 2] 5 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G018.in_snake p P s hr hP

#print axioms word_024_0


end Snake9.ConcreteCatalogue95
