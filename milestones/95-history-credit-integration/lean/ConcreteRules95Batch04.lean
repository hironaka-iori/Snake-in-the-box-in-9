import ConcreteWords95Batch04
import ShareCover04

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule020 : Rule :=
  ⟨signature020, variants020, [], 8, 8⟩

theorem rule_valid_020 : RuleValid rule020 := by
  refine ⟨rfl, share_cover_020, ?_, ?_, ?_⟩
  · simp [rule020]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 2] := by
      simpa [rule020, variants020] using hcs
    rw [heq] at hcanon
    exact word_020_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 2] := by
      simpa [rule020, variants020] using hcs
    rw [heq] at hcanon
    exact word_020_0 p s hr hcanon

#print axioms rule_valid_020

def rule021 : Rule :=
  ⟨signature021, variants021, [], 16, 16⟩

theorem rule_valid_021 : RuleValid rule021 := by
  refine ⟨rfl, share_cover_021, ?_, ?_, ?_⟩
  · simp [rule021]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 0] := by
      simpa [rule021, variants021] using hcs
    rw [heq] at hcanon
    exact word_021_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 0] := by
      simpa [rule021, variants021] using hcs
    rw [heq] at hcanon
    exact word_021_0 p s hr hcanon

#print axioms rule_valid_021

def rule022 : Rule :=
  ⟨signature022, variants022, [], 12, 12⟩

theorem rule_valid_022 : RuleValid rule022 := by
  refine ⟨rfl, share_cover_022, ?_, ?_, ?_⟩
  · simp [rule022]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 4] := by
      simpa [rule022, variants022] using hcs
    rw [heq] at hcanon
    exact word_022_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 4] := by
      simpa [rule022, variants022] using hcs
    rw [heq] at hcanon
    exact word_022_0 p s hr hcanon

#print axioms rule_valid_022

def rule023 : Rule :=
  ⟨signature023, variants023, [], 16, 16⟩

theorem rule_valid_023 : RuleValid rule023 := by
  refine ⟨rfl, share_cover_023, ?_, ?_, ?_⟩
  · simp [rule023]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 6] := by
      simpa [rule023, variants023] using hcs
    rw [heq] at hcanon
    exact word_023_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 6] := by
      simpa [rule023, variants023] using hcs
    rw [heq] at hcanon
    exact word_023_0 p s hr hcanon

#print axioms rule_valid_023

def rule024 : Rule :=
  ⟨signature024, variants024, [], 5, 5⟩

theorem rule_valid_024 : RuleValid rule024 := by
  refine ⟨rfl, share_cover_024, ?_, ?_, ?_⟩
  · simp [rule024]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 1, 0, 4, 2, 5, 3, 2] := by
      simpa [rule024, variants024] using hcs
    rw [heq] at hcanon
    exact word_024_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 1, 0, 4, 2, 5, 3, 2] := by
      simpa [rule024, variants024] using hcs
    rw [heq] at hcanon
    exact word_024_0 p s hr hcanon

#print axioms rule_valid_024


end Snake9.ConcreteCatalogue95
