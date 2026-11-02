import ConcreteWords95Batch00
import ShareCover00

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule000 : Rule :=
  ⟨signature000, variants000, [(1, 2), (2, 2)], 18, 19⟩

theorem rule_valid_000 : RuleValid rule000 := by
  refine ⟨rfl, share_cover_000, ?_, ?_, ?_⟩
  · simp [rule000]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 4, 2, 0, 1, 5, 0] := by
      simpa [rule000, variants000] using hcs
    rw [heq] at hcanon
    exact word_000_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 4, 2, 0, 1, 5, 0] := by
      simpa [rule000, variants000] using hcs
    rw [heq] at hcanon
    exact capped_000_0 p s hr hcanon hcaps

#print axioms rule_valid_000

def rule001 : Rule :=
  ⟨signature001, variants001, [(0, 2)], 32, 36⟩

theorem rule_valid_001 : RuleValid rule001 := by
  refine ⟨rfl, share_cover_001, ?_, ?_, ?_⟩
  · simp [rule001]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 4, 5, 0, 3, 1, 0] := by
      simpa [rule001, variants001] using hcs
    rw [heq] at hcanon
    exact word_001_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 4, 5, 0, 3, 1, 0] := by
      simpa [rule001, variants001] using hcs
    rw [heq] at hcanon
    exact capped_001_0 p s hr hcanon hcaps

#print axioms rule_valid_001

def rule002 : Rule :=
  ⟨signature002, variants002, [(0, 2)], 11, 15⟩

theorem rule_valid_002 : RuleValid rule002 := by
  refine ⟨rfl, share_cover_002, ?_, ?_, ?_⟩
  · simp [rule002]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 4, 5, 0, 3, 2, 0] := by
      simpa [rule002, variants002] using hcs
    rw [heq] at hcanon
    exact word_002_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 4, 5, 0, 3, 2, 0] := by
      simpa [rule002, variants002] using hcs
    rw [heq] at hcanon
    exact capped_002_0 p s hr hcanon hcaps

#print axioms rule_valid_002

def rule003 : Rule :=
  ⟨signature003, variants003, [(2, 2), (3, 2)], 10, 13⟩

theorem rule_valid_003 : RuleValid rule003 := by
  refine ⟨rfl, share_cover_003, ?_, ?_, ?_⟩
  · simp [rule003]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 1, 0, 4, 3, 1, 2, 5] := by
      simpa [rule003, variants003] using hcs
    rw [heq] at hcanon
    exact word_003_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 1, 0, 4, 3, 1, 2, 5] := by
      simpa [rule003, variants003] using hcs
    rw [heq] at hcanon
    exact capped_003_0 p s hr hcanon hcaps

#print axioms rule_valid_003

def rule004 : Rule :=
  ⟨signature004, variants004, [(2, 2), (3, 2)], 19, 26⟩

theorem rule_valid_004 : RuleValid rule004 := by
  refine ⟨rfl, share_cover_004, ?_, ?_, ?_⟩
  · simp [rule004]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 2] := by
      simpa [rule004, variants004] using hcs
    rw [heq] at hcanon
    exact word_004_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 2] := by
      simpa [rule004, variants004] using hcs
    rw [heq] at hcanon
    exact capped_004_0 p s hr hcanon hcaps

#print axioms rule_valid_004


end Snake9.ConcreteCatalogue95
