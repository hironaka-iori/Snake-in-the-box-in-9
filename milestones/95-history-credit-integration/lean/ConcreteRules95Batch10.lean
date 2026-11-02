import ConcreteWords95Batch10
import ShareCover10

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule050 : Rule :=
  ⟨signature050, variants050, [], 20, 20⟩

theorem rule_valid_050 : RuleValid rule050 := by
  refine ⟨rfl, share_cover_050, ?_, ?_, ?_⟩
  · simp [rule050]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 0] ∨ cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 7] := by
      simpa [rule050, variants050] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_050_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_050_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 0] ∨ cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 7] := by
      simpa [rule050, variants050] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_050_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_050_1 p s hr hcanon

#print axioms rule_valid_050

def rule051 : Rule :=
  ⟨signature051, variants051, [], 13, 13⟩

theorem rule_valid_051 : RuleValid rule051 := by
  refine ⟨rfl, share_cover_051, ?_, ?_, ?_⟩
  · simp [rule051]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 5, 3] := by
      simpa [rule051, variants051] using hcs
    rw [heq] at hcanon
    exact word_051_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 3, 2, 6, 5, 3] := by
      simpa [rule051, variants051] using hcs
    rw [heq] at hcanon
    exact word_051_0 p s hr hcanon

#print axioms rule_valid_051

def rule052 : Rule :=
  ⟨signature052, variants052, [], 2, 2⟩

theorem rule_valid_052 : RuleValid rule052 := by
  refine ⟨rfl, share_cover_052, ?_, ?_, ?_⟩
  · simp [rule052]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 2] := by
      simpa [rule052, variants052] using hcs
    rw [heq] at hcanon
    exact word_052_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 2] := by
      simpa [rule052, variants052] using hcs
    rw [heq] at hcanon
    exact word_052_0 p s hr hcanon

#print axioms rule_valid_052

def rule053 : Rule :=
  ⟨signature053, variants053, [], 2, 2⟩

theorem rule_valid_053 : RuleValid rule053 := by
  refine ⟨rfl, share_cover_053, ?_, ?_, ?_⟩
  · simp [rule053]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 7] := by
      simpa [rule053, variants053] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_053_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_053_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 7] := by
      simpa [rule053, variants053] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_053_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_053_1 p s hr hcanon

#print axioms rule_valid_053

def rule054 : Rule :=
  ⟨signature054, variants054, [], 16, 16⟩

theorem rule_valid_054 : RuleValid rule054 := by
  refine ⟨rfl, share_cover_054, ?_, ?_, ?_⟩
  · simp [rule054]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 0] ∨ cs = [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 7] := by
      simpa [rule054, variants054] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_054_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_054_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 0] ∨ cs = [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 7] := by
      simpa [rule054, variants054] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_054_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_054_1 p s hr hcanon

#print axioms rule_valid_054


end Snake9.ConcreteCatalogue95
