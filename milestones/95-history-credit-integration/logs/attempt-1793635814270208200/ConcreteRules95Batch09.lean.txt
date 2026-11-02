import ConcreteWords95Batch09
import ShareCover09

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule045 : Rule :=
  ⟨signature045, variants045, [], 10, 10⟩

theorem rule_valid_045 : RuleValid rule045 := by
  refine ⟨rfl, share_cover_045, ?_, ?_, ?_⟩
  · simp [rule045]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 6] := by
      simpa [rule045, variants045] using hcs
    rw [heq] at hcanon
    exact word_045_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 6] := by
      simpa [rule045, variants045] using hcs
    rw [heq] at hcanon
    exact word_045_0 p s hr hcanon

#print axioms rule_valid_045

def rule046 : Rule :=
  ⟨signature046, variants046, [], 4, 4⟩

theorem rule_valid_046 : RuleValid rule046 := by
  refine ⟨rfl, share_cover_046, ?_, ?_, ?_⟩
  · simp [rule046]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 0, 4, 6] := by
      simpa [rule046, variants046] using hcs
    rw [heq] at hcanon
    exact word_046_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 0, 4, 6] := by
      simpa [rule046, variants046] using hcs
    rw [heq] at hcanon
    exact word_046_0 p s hr hcanon

#print axioms rule_valid_046

def rule047 : Rule :=
  ⟨signature047, variants047, [], 20, 20⟩

theorem rule_valid_047 : RuleValid rule047 := by
  refine ⟨rfl, share_cover_047, ?_, ?_, ?_⟩
  · simp [rule047]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 3] := by
      simpa [rule047, variants047] using hcs
    rw [heq] at hcanon
    exact word_047_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 3] := by
      simpa [rule047, variants047] using hcs
    rw [heq] at hcanon
    exact word_047_0 p s hr hcanon

#print axioms rule_valid_047

def rule048 : Rule :=
  ⟨signature048, variants048, [], 10, 10⟩

theorem rule_valid_048 : RuleValid rule048 := by
  refine ⟨rfl, share_cover_048, ?_, ?_, ?_⟩
  · simp [rule048]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 4] := by
      simpa [rule048, variants048] using hcs
    rw [heq] at hcanon
    exact word_048_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 4] := by
      simpa [rule048, variants048] using hcs
    rw [heq] at hcanon
    exact word_048_0 p s hr hcanon

#print axioms rule_valid_048

def rule049 : Rule :=
  ⟨signature049, variants049, [], 10, 10⟩

theorem rule_valid_049 : RuleValid rule049 := by
  refine ⟨rfl, share_cover_049, ?_, ?_, ?_⟩
  · simp [rule049]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 5] := by
      simpa [rule049, variants049] using hcs
    rw [heq] at hcanon
    exact word_049_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 5] := by
      simpa [rule049, variants049] using hcs
    rw [heq] at hcanon
    exact word_049_0 p s hr hcanon

#print axioms rule_valid_049


end Snake9.ConcreteCatalogue95
