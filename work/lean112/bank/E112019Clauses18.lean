import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 99 = false := by
  rw [value63, value80, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (385 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 102 = false := by
  rw [value63, value80, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (385 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 103 = false := by
  rw [value63, value80, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (385 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 112 = false := by
  rw [value63, value80, value100, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (385 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value63, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 99 = false ∨ valuation q 103 = false := by
  rw [value63, value99, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value63, value99, value100, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (448 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value63, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value63, value100, value102, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 63 = false ∨ valuation q 103 = false ∨ valuation q 112 = false := by
  rw [value63, value100, value103, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value80, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 103 = false := by
  rw [value80, value99, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value80, value99, value100, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (448 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value80, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value80, value100, value102, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 103 = false ∨ valuation q 112 = false := by
  rw [value80, value100, value103, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value99, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value99, value100, value102, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 99 = false ∨ valuation q 103 = false ∨ valuation q 112 = false := by
  rw [value99, value100, value103, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 112 = false := by
  rw [value100, value102, value103, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 63 = true ∨ valuation q 80 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 112 = true := by
  rw [value63, value80, value99, value100, value102, value103, value112, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(321 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (193 : Vertex) [(321 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 41 = true ∨ valuation q 80 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 112 = true := by
  rw [value41, value80, value99, value100, value102, value103, value112, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(193 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (321 : Vertex) [(193 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 41 = true ∨ valuation q 63 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 112 = true := by
  rw [value41, value63, value99, value100, value102, value103, value112, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (385 : Vertex) [(193 : Vertex), (321 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 41 = true ∨ valuation q 63 = true ∨ valuation q 80 = true ∨ valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 112 = true := by
  rw [value41, value63, value80, value100, value102, value103, value112, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex), (385 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (448 : Vertex) [(193 : Vertex), (321 : Vertex), (385 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 41 = true ∨ valuation q 63 = true ∨ valuation q 80 = true ∨ valuation q 99 = true ∨ valuation q 103 = true ∨ valuation q 112 = true := by
  rw [value41, value63, value80, value99, value100, value103, value112, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex), (385 : Vertex), (448 : Vertex), (453 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (451 : Vertex) [(193 : Vertex), (321 : Vertex), (385 : Vertex), (448 : Vertex), (453 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 41 = true ∨ valuation q 63 = true ∨ valuation q 80 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 112 = true := by
  rw [value41, value63, value80, value99, value100, value102, value112, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (453 : Vertex) [(193 : Vertex), (321 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 41 = true ∨ valuation q 63 = true ∨ valuation q 80 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 103 = true := by
  rw [value41, value63, value80, value99, value100, value102, value103, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (465 : Vertex) [(193 : Vertex), (321 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 81 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value81, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 81 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value81, value99, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 81 = false ∨ valuation q 102 = false ∨ valuation q 113 = false := by
  rw [value81, value101, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 113 = false := by
  rw [value99, value101, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (448 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 222 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 113 = true := by
  rw [value99, value101, value102, value113, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(448 : Vertex), (451 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (386 : Vertex) [(448 : Vertex), (451 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E019.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112019
