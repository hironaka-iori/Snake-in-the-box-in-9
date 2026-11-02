import ConcreteWords95Batch02
import ShareCover02

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def rule010 : Rule :=
  ⟨signature010, variants010, [], 4, 4⟩

theorem rule_valid_010 : RuleValid rule010 := by
  refine ⟨rfl, share_cover_010, ?_, ?_, ?_⟩
  · simp [rule010]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 1] ∨ cs = [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 6] := by
      simpa [rule010, variants010] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_010_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_010_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 1] ∨ cs = [0, 1, 2, 0, 3, 2, 4, 5, 2, 3, 6] := by
      simpa [rule010, variants010] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_010_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_010_1 p s hr hcanon

#print axioms rule_valid_010

def rule011 : Rule :=
  ⟨signature011, variants011, [], 2, 2⟩

theorem rule_valid_011 : RuleValid rule011 := by
  refine ⟨rfl, share_cover_011, ?_, ?_, ?_⟩
  · simp [rule011]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 2, 4, 5, 6, 4, 2] := by
      simpa [rule011, variants011] using hcs
    rw [heq] at hcanon
    exact word_011_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 2, 4, 5, 6, 4, 2] := by
      simpa [rule011, variants011] using hcs
    rw [heq] at hcanon
    exact word_011_0 p s hr hcanon

#print axioms rule_valid_011

def rule012 : Rule :=
  ⟨signature012, variants012, [], 20, 20⟩

theorem rule_valid_012 : RuleValid rule012 := by
  refine ⟨rfl, share_cover_012, ?_, ?_, ?_⟩
  · simp [rule012]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 4, 0, 2, 5, 1, 0] := by
      simpa [rule012, variants012] using hcs
    rw [heq] at hcanon
    exact word_012_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 4, 0, 2, 5, 1, 0] := by
      simpa [rule012, variants012] using hcs
    rw [heq] at hcanon
    exact word_012_0 p s hr hcanon

#print axioms rule_valid_012

def rule013 : Rule :=
  ⟨signature013, variants013, [], 6, 6⟩

theorem rule_valid_013 : RuleValid rule013 := by
  refine ⟨rfl, share_cover_013, ?_, ?_, ?_⟩
  · simp [rule013]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 0, 3, 4, 0, 2, 5, 0, 1] ∨ cs = [0, 1, 2, 0, 3, 4, 0, 2, 5, 0, 6] := by
      simpa [rule013, variants013] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_013_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_013_1 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 0, 3, 4, 0, 2, 5, 0, 1] ∨ cs = [0, 1, 2, 0, 3, 4, 0, 2, 5, 0, 6] := by
      simpa [rule013, variants013] using hcs
    rcases heq with heq | heq
    · rw [heq] at hcanon
      exact word_013_0 p s hr hcanon
    · rw [heq] at hcanon
      exact word_013_1 p s hr hcanon

#print axioms rule_valid_013

def rule014 : Rule :=
  ⟨signature014, variants014, [], 9, 9⟩

theorem rule_valid_014 : RuleValid rule014 := by
  refine ⟨rfl, share_cover_014, ?_, ?_, ?_⟩
  · simp [rule014]
  · intro cs hcs m p s hr hcanon
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 2] := by
      simpa [rule014, variants014] using hcs
    rw [heq] at hcanon
    exact word_014_0 p s hr hcanon
  · intro cs hcs m p s hr hcanon hcaps
    have heq : cs = [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 2] := by
      simpa [rule014, variants014] using hcs
    rw [heq] at hcanon
    exact word_014_0 p s hr hcanon

#print axioms rule_valid_014


end Snake9.ConcreteCatalogue95
