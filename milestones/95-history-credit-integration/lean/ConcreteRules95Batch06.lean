import ConcreteWords95Batch06
import ShareCover06

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule030 : Rule :=
  ⟨signature030, variants030, [], 2, 2⟩

theorem rule_valid_030 : RuleValid rule030 := by
  refine ⟨rfl, share_cover_030, ?_, ?_, ?_⟩
  · simp [rule030]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 2] := by
      simpa [rule030, variants030] using hcs
    rw [heq] at hcanon
    exact word_030_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 2] := by
      simpa [rule030, variants030] using hcs
    rw [heq] at hcanon
    exact word_030_0 p s hr hcanon

#print axioms rule_valid_030

def rule031 : Rule :=
  ⟨signature031, variants031, [], 2, 2⟩

theorem rule_valid_031 : RuleValid rule031 := by
  refine ⟨rfl, share_cover_031, ?_, ?_, ?_⟩
  · simp [rule031]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 6] := by
      simpa [rule031, variants031] using hcs
    rw [heq] at hcanon
    exact word_031_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 0, 5, 1, 0, 4, 6] := by
      simpa [rule031, variants031] using hcs
    rw [heq] at hcanon
    exact word_031_0 p s hr hcanon

#print axioms rule_valid_031

def rule032 : Rule :=
  ⟨signature032, variants032, [], 7, 7⟩

theorem rule_valid_032 : RuleValid rule032 := by
  refine ⟨rfl, share_cover_032, ?_, ?_, ?_⟩
  · simp [rule032]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 0, 5, 4, 3, 1, 6] := by
      simpa [rule032, variants032] using hcs
    rw [heq] at hcanon
    exact word_032_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 0, 5, 4, 3, 1, 6] := by
      simpa [rule032, variants032] using hcs
    rw [heq] at hcanon
    exact word_032_0 p s hr hcanon

#print axioms rule_valid_032

def rule033 : Rule :=
  ⟨signature033, variants033, [], 16, 16⟩

theorem rule_valid_033 : RuleValid rule033 := by
  refine ⟨rfl, share_cover_033, ?_, ?_, ?_⟩
  · simp [rule033]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 6] := by
      simpa [rule033, variants033] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_033_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_033_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 6] := by
      simpa [rule033, variants033] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_033_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_033_1 p s hr hcanon

#print axioms rule_valid_033

def rule034 : Rule :=
  ⟨signature034, variants034, [], 4, 4⟩

theorem rule_valid_034 : RuleValid rule034 := by
  refine ⟨rfl, share_cover_034, ?_, ?_, ?_⟩
  · simp [rule034]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 1, 2, 5, 6, 2, 1] := by
      simpa [rule034, variants034] using hcs
    rw [heq] at hcanon
    exact word_034_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 1, 2, 5, 6, 2, 1] := by
      simpa [rule034, variants034] using hcs
    rw [heq] at hcanon
    exact word_034_0 p s hr hcanon

#print axioms rule_valid_034


end Snake9.ConcreteCatalogue95
