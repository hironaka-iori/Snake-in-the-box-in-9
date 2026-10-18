import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value27, value102, value108, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value62, value91, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value62, value91, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 91 = false ∨ valuation q 108 = false := by
  rw [value62, value91, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 91 = false ∨ valuation q 123 = false := by
  rw [value62, value91, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value62, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value62, value100, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (405 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 100 = false ∨ valuation q 123 = false := by
  rw [value62, value100, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (405 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value62, value101, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 101 = false ∨ valuation q 123 = false := by
  rw [value62, value101, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 62 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value62, value102, value108, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value91, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value91, value100, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 123 = false := by
  rw [value91, value100, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 91 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value91, value101, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 91 = false ∨ valuation q 101 = false ∨ valuation q 123 = false := by
  rw [value91, value101, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 91 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value91, value102, value108, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value100, value101, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (405 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 123 = false := by
  rw [value100, value101, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (405 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 100 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value100, value102, value108, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (405 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 101 = false ∨ valuation q 108 = false ∨ valuation q 123 = false := by
  rw [value101, value102, value108, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (406 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 62 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 108 = true ∨ valuation q 123 = true := by
  rw [value62, value91, value100, value101, value102, value108, value123, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(279 : Vertex), (391 : Vertex), (405 : Vertex), (406 : Vertex), (415 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (151 : Vertex) [(279 : Vertex), (391 : Vertex), (405 : Vertex), (406 : Vertex), (415 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 27 = true ∨ valuation q 62 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 108 = true ∨ valuation q 123 = true := by
  rw [value27, value62, value100, value101, value102, value108, value123, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(151 : Vertex), (279 : Vertex), (405 : Vertex), (406 : Vertex), (415 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (391 : Vertex) [(151 : Vertex), (279 : Vertex), (405 : Vertex), (406 : Vertex), (415 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 27 = true ∨ valuation q 62 = true ∨ valuation q 91 = true ∨ valuation q 101 = true ∨ valuation q 108 = true ∨ valuation q 123 = true := by
  rw [value27, value62, value91, value101, value102, value108, value123, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(151 : Vertex), (279 : Vertex), (391 : Vertex), (406 : Vertex), (415 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (405 : Vertex) [(151 : Vertex), (279 : Vertex), (391 : Vertex), (406 : Vertex), (415 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 27 = true ∨ valuation q 62 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 108 = true ∨ valuation q 123 = true := by
  rw [value27, value62, value91, value100, value102, value108, value123, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(151 : Vertex), (279 : Vertex), (391 : Vertex), (405 : Vertex), (415 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (406 : Vertex) [(151 : Vertex), (279 : Vertex), (391 : Vertex), (405 : Vertex), (415 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 27 = true ∨ valuation q 62 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 123 = true := by
  rw [value27, value62, value91, value100, value101, value102, value123, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(151 : Vertex), (279 : Vertex), (391 : Vertex), (405 : Vertex), (406 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (415 : Vertex) [(151 : Vertex), (279 : Vertex), (391 : Vertex), (405 : Vertex), (406 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 105 = false := by
  rw [value93, value98, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value93, value98, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 93 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value93, value103, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 98 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value98, value103, value105, value106, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (393 : Vertex) [(401 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 93 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value93, value103, value105, value106, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(393 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(393 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 231 = true ∨ valuation q 93 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value93, value98, value103, value106, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(393 : Vertex), (401 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E050.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112050
