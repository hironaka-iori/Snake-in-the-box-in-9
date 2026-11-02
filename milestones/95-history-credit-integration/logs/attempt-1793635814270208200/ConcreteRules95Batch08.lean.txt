import ConcreteWords95Batch08
import ShareCover08

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule040 : Rule :=
  ⟨signature040, variants040, [], 5, 5⟩

theorem rule_valid_040 : RuleValid rule040 := by
  refine ⟨rfl, share_cover_040, ?_, ?_, ?_⟩
  · simp [rule040]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 7] := by
      simpa [rule040, variants040] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_040_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_040_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 7] := by
      simpa [rule040, variants040] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_040_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_040_1 p s hr hcanon

#print axioms rule_valid_040

def rule041 : Rule :=
  ⟨signature041, variants041, [], 7, 7⟩

theorem rule_valid_041 : RuleValid rule041 := by
  refine ⟨rfl, share_cover_041, ?_, ?_, ?_⟩
  · simp [rule041]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 0, 4, 3, 1, 6] := by
      simpa [rule041, variants041] using hcs
    rw [heq] at hcanon
    exact word_041_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 0, 4, 3, 1, 6] := by
      simpa [rule041, variants041] using hcs
    rw [heq] at hcanon
    exact word_041_0 p s hr hcanon

#print axioms rule_valid_041

def rule042 : Rule :=
  ⟨signature042, variants042, [], 2, 2⟩

theorem rule_valid_042 : RuleValid rule042 := by
  refine ⟨rfl, share_cover_042, ?_, ?_, ?_⟩
  · simp [rule042]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 2] := by
      simpa [rule042, variants042] using hcs
    rw [heq] at hcanon
    exact word_042_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 2] := by
      simpa [rule042, variants042] using hcs
    rw [heq] at hcanon
    exact word_042_0 p s hr hcanon

#print axioms rule_valid_042

def rule043 : Rule :=
  ⟨signature043, variants043, [], 2, 2⟩

theorem rule_valid_043 : RuleValid rule043 := by
  refine ⟨rfl, share_cover_043, ?_, ?_, ?_⟩
  · simp [rule043]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 7] := by
      simpa [rule043, variants043] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_043_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_043_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 7] := by
      simpa [rule043, variants043] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_043_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_043_1 p s hr hcanon

#print axioms rule_valid_043

def rule044 : Rule :=
  ⟨signature044, variants044, [], 15, 15⟩

theorem rule_valid_044 : RuleValid rule044 := by
  refine ⟨rfl, share_cover_044, ?_, ?_, ?_⟩
  · simp [rule044]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 2, 3, 6, 2, 5] := by
      simpa [rule044, variants044] using hcs
    rw [heq] at hcanon
    exact word_044_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 2, 3, 6, 2, 5] := by
      simpa [rule044, variants044] using hcs
    rw [heq] at hcanon
    exact word_044_0 p s hr hcanon

#print axioms rule_valid_044


end Snake9.ConcreteCatalogue95
