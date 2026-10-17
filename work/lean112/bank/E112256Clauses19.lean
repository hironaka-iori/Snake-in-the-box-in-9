import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 84 = true := by
  rw [value84, value95, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(338 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (498 : Vertex) [(338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 223 = true ∨ valuation q 97 = true ∨ valuation q 99 = true ∨ valuation q 121 = true := by
  rw [value96, value97, value99, value121, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(375 : Vertex), (381 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (341 : Vertex) [(375 : Vertex), (381 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 223 = true ∨ valuation q 85 = true ∨ valuation q 99 = true ∨ valuation q 121 = true := by
  rw [value85, value96, value99, value121, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(341 : Vertex), (381 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (375 : Vertex) [(341 : Vertex), (381 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 223 = true ∨ valuation q 85 = true ∨ valuation q 97 = true ∨ valuation q 99 = true := by
  rw [value85, value96, value97, value99, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(341 : Vertex), (375 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (501 : Vertex) [(341 : Vertex), (375 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value96, value97, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (375 : Vertex) (373 : Vertex) (383 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 101 = true ∨ valuation q 122 = true := by
  rw [value97, value101, value122, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(383 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(383 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 96 = true ∨ valuation q 101 = true := by
  rw [value96, value97, value101, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(373 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (503 : Vertex) [(373 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 124 = true := by
  rw [value98, value101, value124, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(383 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (347 : Vertex) [(383 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 76 = false ∨ valuation q 90 = false := by
  rw [value33, value76, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (317 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 76 = false ∨ valuation q 93 = false := by
  rw [value33, value76, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (317 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 76 = false ∨ valuation q 96 = false := by
  rw [value33, value76, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (317 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 76 = false ∨ valuation q 101 = false := by
  rw [value33, value76, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (317 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 76 = false ∨ valuation q 126 = false := by
  rw [value33, value76, value99, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (317 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 90 = false ∨ valuation q 101 = false := by
  rw [value33, value90, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (349 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value33, value93, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (365 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value33, value93, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (365 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 33 = false ∨ valuation q 96 = false ∨ valuation q 101 = false := by
  rw [value33, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (373 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 76 = false ∨ valuation q 90 = false ∨ valuation q 101 = false := by
  rw [value76, value90, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (349 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 76 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value76, value93, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (365 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 76 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value76, value93, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (365 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 76 = false ∨ valuation q 93 = false ∨ valuation q 126 = false := by
  rw [value76, value93, value99, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (365 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 76 = false ∨ valuation q 96 = false ∨ valuation q 101 = false := by
  rw [value76, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (373 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 76 = false ∨ valuation q 96 = false ∨ valuation q 126 = false := by
  rw [value76, value96, value99, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (373 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 76 = false ∨ valuation q 101 = false ∨ valuation q 126 = false := by
  rw [value76, value99, value101, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (383 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value90, value93, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (349 : Vertex) (365 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value90, value93, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (349 : Vertex) (365 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 90 = false ∨ valuation q 96 = false ∨ valuation q 101 = false := by
  rw [value90, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (349 : Vertex) (373 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 90 = false ∨ valuation q 101 = false ∨ valuation q 126 = false := by
  rw [value90, value99, value101, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (349 : Vertex) (383 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 101 = false := by
  rw [value93, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (365 : Vertex) (373 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 126 = false := by
  rw [value93, value96, value99, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (365 : Vertex) (373 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 101 = false ∨ valuation q 126 = false := by
  rw [value93, value99, value101, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (365 : Vertex) (383 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = false ∨ valuation q 101 = false ∨ valuation q 126 = false := by
  rw [value96, value99, value101, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (373 : Vertex) (383 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E256.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112256
