import CreditTransport95
import HistoryCreditEvaluator95
import Port95M61GeometryBatch04
import Port95M63Edge045
import Port95M64Edge007
import Port95M64Edge010
import Port95M64Edge011
import Port95M65Edge007
import Port95M65Edge010
import Port95M65Edge011
import Port95M65Edge044
import Port95M65Edge045
import SuffixCredit95

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

theorem word_000_0 : WordShareBound [0, 1, 2, 0, 3, 4, 2, 0, 1, 5, 0] 18 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.NeighbourChoice64.E007.in_snake p P s hr hP

#print axioms word_000_0

theorem capped_000_0 : WordCappedShareBound [0, 1, 2, 0, 3, 4, 2, 0, 1, 5, 0] [(1, 2), (2, 2)] 19 := by
  apply word_capped_share_of_local _ _ Snake9.LocalWindow.CountPropagationPort95.E007.bounds _ rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro k hk
      interval_cases k <;> norm_num [Snake9.LocalWindow.CountPropagationPort95.E007.bounds]
  · intro m p P s hr hP hb
    exact Snake9.LocalWindow.CountPropagationPort95.E007.in_snake p P s hr hP hb

#print axioms capped_000_0

theorem word_001_0 : WordShareBound [0, 1, 2, 0, 3, 4, 5, 0, 3, 1, 0] 32 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.NeighbourChoice64.E010.in_snake p P s hr hP

#print axioms word_001_0

theorem capped_001_0 : WordCappedShareBound [0, 1, 2, 0, 3, 4, 5, 0, 3, 1, 0] [(0, 2)] 36 := by
  apply word_capped_share_of_local _ _ Snake9.LocalWindow.CountPropagationPort95.E010.bounds _ rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro k hk
      interval_cases k <;> norm_num [Snake9.LocalWindow.CountPropagationPort95.E010.bounds]
  · intro m p P s hr hP hb
    exact Snake9.LocalWindow.CountPropagationPort95.E010.in_snake p P s hr hP hb

#print axioms capped_001_0

theorem word_002_0 : WordShareBound [0, 1, 2, 0, 3, 4, 5, 0, 3, 2, 0] 11 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.NeighbourChoice64.E011.in_snake p P s hr hP

#print axioms word_002_0

theorem capped_002_0 : WordCappedShareBound [0, 1, 2, 0, 3, 4, 5, 0, 3, 2, 0] [(0, 2)] 15 := by
  apply word_capped_share_of_local _ _ Snake9.LocalWindow.CountPropagationPort95.E011.bounds _ rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro k hk
      interval_cases k <;> norm_num [Snake9.LocalWindow.CountPropagationPort95.E011.bounds]
  · intro m p P s hr hP hb
    exact Snake9.LocalWindow.CountPropagationPort95.E011.in_snake p P s hr hP hb

#print axioms capped_002_0

theorem word_003_0 : WordShareBound [0, 1, 2, 3, 1, 0, 4, 3, 1, 2, 5] 10 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.FamilyShare61.G154.in_snake p P s hr hP

#print axioms word_003_0

theorem capped_003_0 : WordCappedShareBound [0, 1, 2, 3, 1, 0, 4, 3, 1, 2, 5] [(2, 2), (3, 2)] 13 := by
  apply word_capped_share_of_local _ _ Snake9.LocalWindow.CountPropagationPort95.E044.bounds _ rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro k hk
      interval_cases k <;> norm_num [Snake9.LocalWindow.CountPropagationPort95.E044.bounds]
  · intro m p P s hr hP hb
    exact Snake9.LocalWindow.CountPropagationPort95.E044.in_snake p P s hr hP hb

#print axioms capped_003_0

theorem word_004_0 : WordShareBound [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 2] 19 := by
  apply word_share_of_local _ _ rfl
  intro m p P s hr hP
  exact Snake9.LocalWindow.LongWindow63.E045.in_snake p P s hr hP

#print axioms word_004_0

theorem capped_004_0 : WordCappedShareBound [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 2] [(2, 2), (3, 2)] 26 := by
  apply word_capped_share_of_local _ _ Snake9.LocalWindow.CountPropagationPort95.E045.bounds _ rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro k hk
      interval_cases k <;> norm_num [Snake9.LocalWindow.CountPropagationPort95.E045.bounds]
  · intro m p P s hr hP hb
    exact Snake9.LocalWindow.CountPropagationPort95.E045.in_snake p P s hr hP hb

#print axioms capped_004_0


end Snake9.ConcreteCatalogue95
