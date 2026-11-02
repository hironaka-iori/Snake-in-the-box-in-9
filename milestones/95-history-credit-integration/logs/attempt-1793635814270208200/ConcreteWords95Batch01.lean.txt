import CreditTransport95
import HistoryCreditEvaluator95
import Port95M61GeometryBatch07
import Port95M62Edge27
import Port95M63Edge057
import Port95M65Edge057
import Port95M65Edge058
import Port95M65Edge091
import Port95M67ChargeBatch00
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_005_0 : WordShareBound [0, 1, 2, 3, 4, 0, 3, 2, 5, 1, 3] 22 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.LongWindow63.E057.in_snake p P s hr hP

#print axioms word_005_0

theorem capped_005_0 : WordCappedShareBound [0, 1, 2, 3, 4, 0, 3, 2, 5, 1, 3] [(3, 2)] 26 := by
  apply word_capped_share_of_local _ _ Snake9.LocalWindow.CountPropagationPort95.E057.bounds _ rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro k hk
      interval_cases k <;> norm_num [Snake9.LocalWindow.CountPropagationPort95.E057.bounds]
  · intro m p P s hr hP hb
    exact Snake9.LocalWindow.CountPropagationPort95.E057.in_snake p P s hr hP hb

#print axioms capped_005_0

theorem word_006_0 : WordShareBound [0, 1, 2, 3, 4, 0, 3, 2, 5, 6, 3] 6 := by
  apply word_share_of_final_nine _ Snake9.LocalWindow.SplitShare62.E27.ds _ rfl
  · decide +kernel
  · intro m p P s hr hP
    exact Snake9.LocalWindow.SplitShare62.E27.in_snake p P s hr hP

#print axioms word_006_0

theorem capped_006_0 : WordCappedShareBound [0, 1, 2, 3, 4, 0, 3, 2, 5, 6, 3] [(3, 2)] 12 := by
  apply word_capped_share_of_local _ _ Snake9.LocalWindow.CountPropagationPort95.E058.bounds _ rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro k hk
      interval_cases k <;> norm_num [Snake9.LocalWindow.CountPropagationPort95.E058.bounds]
  · intro m p P s hr hP hb
    exact Snake9.LocalWindow.CountPropagationPort95.E058.in_snake p P s hr hP hb

#print axioms capped_006_0

theorem word_007_0 : WordShareBound [0, 1, 2, 3, 4, 2, 1, 5, 0, 3, 6] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyShare61.G200.in_snake p P s hr hP

#print axioms word_007_0

theorem capped_007_0 : WordCappedShareBound [0, 1, 2, 3, 4, 2, 1, 5, 0, 3, 6] [(0, 1), (3, 5), (4, 1)] 5 := by
  apply word_capped_share_of_local _ _ Snake9.LocalWindow.CountPropagationPort95.E091.bounds _ rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro k hk
      interval_cases k <;> norm_num [Snake9.LocalWindow.CountPropagationPort95.E091.bounds]
  · intro m p P s hr hP hb
    exact Snake9.LocalWindow.CountPropagationPort95.E091.in_snake p P s hr hP hb

#print axioms capped_007_0

theorem word_008_0 : WordShareBound [0, 1, 2, 0, 3, 2, 4, 5, 1, 4, 2] 2 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G000.in_snake p P s hr hP

#print axioms word_008_0

theorem word_009_0 : WordShareBound [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 0] 4 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyCharge67.G001.in_snake p P s hr hP

#print axioms word_009_0


end Snake9.ConcreteCatalogue95
