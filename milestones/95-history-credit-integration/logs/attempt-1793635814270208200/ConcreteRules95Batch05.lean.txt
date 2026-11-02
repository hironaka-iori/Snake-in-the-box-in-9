import ConcreteWords95Batch05
import ShareCover05

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule025 : Rule :=
  ⟨signature025, variants025, [], 13, 13⟩

theorem rule_valid_025 : RuleValid rule025 := by
  refine ⟨rfl, share_cover_025, ?_, ?_, ?_⟩
  · simp [rule025]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 6] := by
      simpa [rule025, variants025] using hcs
    rw [heq] at hcanon
    exact word_025_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 6] := by
      simpa [rule025, variants025] using hcs
    rw [heq] at hcanon
    exact word_025_0 p s hr hcanon

#print axioms rule_valid_025

def rule026 : Rule :=
  ⟨signature026, variants026, [], 2, 2⟩

theorem rule_valid_026 : RuleValid rule026 := by
  refine ⟨rfl, share_cover_026, ?_, ?_, ?_⟩
  · simp [rule026]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 1, 4, 5, 0, 4, 1, 6] := by
      simpa [rule026, variants026] using hcs
    rw [heq] at hcanon
    exact word_026_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 1, 4, 5, 0, 4, 1, 6] := by
      simpa [rule026, variants026] using hcs
    rw [heq] at hcanon
    exact word_026_0 p s hr hcanon

#print axioms rule_valid_026

def rule027 : Rule :=
  ⟨signature027, variants027, [], 5, 5⟩

theorem rule_valid_027 : RuleValid rule027 := by
  refine ⟨rfl, share_cover_027, ?_, ?_, ?_⟩
  · simp [rule027]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 1, 4, 5, 1, 3, 2, 1] := by
      simpa [rule027, variants027] using hcs
    rw [heq] at hcanon
    exact word_027_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 1, 4, 5, 1, 3, 2, 1] := by
      simpa [rule027, variants027] using hcs
    rw [heq] at hcanon
    exact word_027_0 p s hr hcanon

#print axioms rule_valid_027

def rule028 : Rule :=
  ⟨signature028, variants028, [], 4, 4⟩

theorem rule_valid_028 : RuleValid rule028 := by
  refine ⟨rfl, share_cover_028, ?_, ?_, ?_⟩
  · simp [rule028]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 1, 4, 5, 1, 3, 0, 1] ∨ cs = [0, 1, 2, 3, 1, 4, 5, 1, 3, 6, 1] := by
      simpa [rule028, variants028] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_028_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_028_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 1, 4, 5, 1, 3, 0, 1] ∨ cs = [0, 1, 2, 3, 1, 4, 5, 1, 3, 6, 1] := by
      simpa [rule028, variants028] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_028_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_028_1 p s hr hcanon

#print axioms rule_valid_028

def rule029 : Rule :=
  ⟨signature029, variants029, [], 2, 2⟩

theorem rule_valid_029 : RuleValid rule029 := by
  refine ⟨rfl, share_cover_029, ?_, ?_, ?_⟩
  · simp [rule029]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 1, 4, 5, 6, 4, 1, 0] ∨ cs = [0, 1, 2, 3, 1, 4, 5, 6, 4, 1, 7] := by
      simpa [rule029, variants029] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_029_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_029_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 1, 4, 5, 6, 4, 1, 0] ∨ cs = [0, 1, 2, 3, 1, 4, 5, 6, 4, 1, 7] := by
      simpa [rule029, variants029] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_029_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_029_1 p s hr hcanon

#print axioms rule_valid_029


end Snake9.ConcreteCatalogue95
