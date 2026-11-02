import ConcreteWords95Batch01
import ShareCover01

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule005 : Rule :=
  ⟨signature005, variants005, [(3, 2)], 22, 26⟩

theorem rule_valid_005 : RuleValid rule005 := by
  refine ⟨rfl, share_cover_005, ?_, ?_, ?_⟩
  · simp [rule005]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 0, 3, 2, 5, 1, 3] := by
      simpa [rule005, variants005] using hcs
    rw [heq] at hcanon
    exact word_005_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 0, 3, 2, 5, 1, 3] := by
      simpa [rule005, variants005] using hcs
    rw [heq] at hcanon
    exact capped_005_0 p s hr hcanon hcaps

#print axioms rule_valid_005

def rule006 : Rule :=
  ⟨signature006, variants006, [(3, 2)], 6, 12⟩

theorem rule_valid_006 : RuleValid rule006 := by
  refine ⟨rfl, share_cover_006, ?_, ?_, ?_⟩
  · simp [rule006]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 0, 3, 2, 5, 6, 3] := by
      simpa [rule006, variants006] using hcs
    rw [heq] at hcanon
    exact word_006_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 0, 3, 2, 5, 6, 3] := by
      simpa [rule006, variants006] using hcs
    rw [heq] at hcanon
    exact capped_006_0 p s hr hcanon hcaps

#print axioms rule_valid_006

def rule007 : Rule :=
  ⟨signature007, variants007, [(0, 1), (3, 5), (4, 1)], 4, 5⟩

theorem rule_valid_007 : RuleValid rule007 := by
  refine ⟨rfl, share_cover_007, ?_, ?_, ?_⟩
  · simp [rule007]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 0, 3, 6] := by
      simpa [rule007, variants007] using hcs
    rw [heq] at hcanon
    exact word_007_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 0, 3, 6] := by
      simpa [rule007, variants007] using hcs
    rw [heq] at hcanon
    exact capped_007_0 p s hr hcanon hcaps

#print axioms rule_valid_007

def rule008 : Rule :=
  ⟨signature008, variants008, [], 2, 2⟩

theorem rule_valid_008 : RuleValid rule008 := by
  refine ⟨rfl, share_cover_008, ?_, ?_, ?_⟩
  · simp [rule008]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 2, 4, 5, 1, 4, 2] := by
      simpa [rule008, variants008] using hcs
    rw [heq] at hcanon
    exact word_008_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 2, 4, 5, 1, 4, 2] := by
      simpa [rule008, variants008] using hcs
    rw [heq] at hcanon
    exact word_008_0 p s hr hcanon

#print axioms rule_valid_008

def rule009 : Rule :=
  ⟨signature009, variants009, [], 4, 4⟩

theorem rule_valid_009 : RuleValid rule009 := by
  refine ⟨rfl, share_cover_009, ?_, ?_, ?_⟩
  · simp [rule009]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 0] := by
      simpa [rule009, variants009] using hcs
    rw [heq] at hcanon
    exact word_009_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 0] := by
      simpa [rule009, variants009] using hcs
    rw [heq] at hcanon
    exact word_009_0 p s hr hcanon

#print axioms rule_valid_009


end Snake9.ConcreteCatalogue95
