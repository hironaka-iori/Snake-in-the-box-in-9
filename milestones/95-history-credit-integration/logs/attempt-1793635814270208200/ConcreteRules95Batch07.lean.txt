import ConcreteWords95Batch07
import ShareCover07

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule035 : Rule :=
  ⟨signature035, variants035, [], 4, 4⟩

theorem rule_valid_035 : RuleValid rule035 := by
  refine ⟨rfl, share_cover_035, ?_, ?_, ?_⟩
  · simp [rule035]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 0, 4, 6] := by
      simpa [rule035, variants035] using hcs
    rw [heq] at hcanon
    exact word_035_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 0, 4, 6] := by
      simpa [rule035, variants035] using hcs
    rw [heq] at hcanon
    exact word_035_0 p s hr hcanon

#print axioms rule_valid_035

def rule036 : Rule :=
  ⟨signature036, variants036, [], 7, 7⟩

theorem rule_valid_036 : RuleValid rule036 := by
  refine ⟨rfl, share_cover_036, ?_, ?_, ?_⟩
  · simp [rule036]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 6] := by
      simpa [rule036, variants036] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_036_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_036_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 0] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 6] := by
      simpa [rule036, variants036] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_036_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_036_1 p s hr hcanon

#print axioms rule_valid_036

def rule037 : Rule :=
  ⟨signature037, variants037, [], 6, 6⟩

theorem rule_valid_037 : RuleValid rule037 := by
  refine ⟨rfl, share_cover_037, ?_, ?_, ?_⟩
  · simp [rule037]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 2, 0, 5] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 2, 6, 5] := by
      simpa [rule037, variants037] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_037_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_037_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 2, 0, 5] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 2, 6, 5] := by
      simpa [rule037, variants037] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_037_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_037_1 p s hr hcanon

#print axioms rule_valid_037

def rule038 : Rule :=
  ⟨signature038, variants038, [], 14, 14⟩

theorem rule_valid_038 : RuleValid rule038 := by
  refine ⟨rfl, share_cover_038, ?_, ?_, ?_⟩
  · simp [rule038]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 0] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 6] := by
      simpa [rule038, variants038] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_038_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_038_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 0] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 6] := by
      simpa [rule038, variants038] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_038_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_038_1 p s hr hcanon

#print axioms rule_valid_038

def rule039 : Rule :=
  ⟨signature039, variants039, [], 5, 5⟩

theorem rule_valid_039 : RuleValid rule039 := by
  refine ⟨rfl, share_cover_039, ?_, ?_, ?_⟩
  · simp [rule039]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 0] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 7] := by
      simpa [rule039, variants039] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_039_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_039_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 0] ∨ cs = [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 7] := by
      simpa [rule039, variants039] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_039_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_039_1 p s hr hcanon

#print axioms rule_valid_039


end Snake9.ConcreteCatalogue95
