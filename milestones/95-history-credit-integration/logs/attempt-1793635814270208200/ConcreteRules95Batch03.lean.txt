import ConcreteWords95Batch03
import ShareCover03

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule015 : Rule :=
  ⟨signature015, variants015, [], 9, 9⟩

theorem rule_valid_015 : RuleValid rule015 := by
  refine ⟨rfl, share_cover_015, ?_, ?_, ?_⟩
  · simp [rule015]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 6] := by
      simpa [rule015, variants015] using hcs
    rw [heq] at hcanon
    exact word_015_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 6] := by
      simpa [rule015, variants015] using hcs
    rw [heq] at hcanon
    exact word_015_0 p s hr hcanon

#print axioms rule_valid_015

def rule016 : Rule :=
  ⟨signature016, variants016, [], 2, 2⟩

theorem rule_valid_016 : RuleValid rule016 := by
  refine ⟨rfl, share_cover_016, ?_, ?_, ?_⟩
  · simp [rule016]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 2] := by
      simpa [rule016, variants016] using hcs
    rw [heq] at hcanon
    exact word_016_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 2] := by
      simpa [rule016, variants016] using hcs
    rw [heq] at hcanon
    exact word_016_0 p s hr hcanon

#print axioms rule_valid_016

def rule017 : Rule :=
  ⟨signature017, variants017, [], 2, 2⟩

theorem rule_valid_017 : RuleValid rule017 := by
  refine ⟨rfl, share_cover_017, ?_, ?_, ?_⟩
  · simp [rule017]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 3] := by
      simpa [rule017, variants017] using hcs
    rw [heq] at hcanon
    exact word_017_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 3] := by
      simpa [rule017, variants017] using hcs
    rw [heq] at hcanon
    exact word_017_0 p s hr hcanon

#print axioms rule_valid_017

def rule018 : Rule :=
  ⟨signature018, variants018, [], 2, 2⟩

theorem rule_valid_018 : RuleValid rule018 := by
  refine ⟨rfl, share_cover_018, ?_, ?_, ?_⟩
  · simp [rule018]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 6] := by
      simpa [rule018, variants018] using hcs
    rw [heq] at hcanon
    exact word_018_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 6] := by
      simpa [rule018, variants018] using hcs
    rw [heq] at hcanon
    exact word_018_0 p s hr hcanon

#print axioms rule_valid_018

def rule019 : Rule :=
  ⟨signature019, variants019, [], 13, 13⟩

theorem rule_valid_019 : RuleValid rule019 := by
  refine ⟨rfl, share_cover_019, ?_, ?_, ?_⟩
  · simp [rule019]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 4, 3, 2, 5, 1, 2] := by
      simpa [rule019, variants019] using hcs
    rw [heq] at hcanon
    exact word_019_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 4, 3, 2, 5, 1, 2] := by
      simpa [rule019, variants019] using hcs
    rw [heq] at hcanon
    exact word_019_0 p s hr hcanon

#print axioms rule_valid_019


end Snake9.ConcreteCatalogue95
