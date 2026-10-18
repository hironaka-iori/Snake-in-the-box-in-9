import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 124 = false := by
  rw [value93, value103, value104, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (394 : Vertex) (411 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 124 = false := by
  rw [value103, value104, value106, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (411 : Vertex) (414 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 124 = true := by
  rw [value103, value104, value106, value124, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(411 : Vertex), (414 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (394 : Vertex) [(411 : Vertex), (414 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 93 = true ∨ valuation q 106 = true ∨ valuation q 124 = true := by
  rw [value93, value103, value106, value124, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(394 : Vertex), (414 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (411 : Vertex) [(394 : Vertex), (414 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 93 = true ∨ valuation q 104 = true ∨ valuation q 124 = true := by
  rw [value93, value103, value104, value124, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(394 : Vertex), (411 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (414 : Vertex) [(394 : Vertex), (411 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 93 = true ∨ valuation q 104 = true ∨ valuation q 106 = true := by
  rw [value93, value103, value104, value106, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(394 : Vertex), (411 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (474 : Vertex) [(394 : Vertex), (411 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 94 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value94, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 94 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value94, value102, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 94 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value94, value103, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value102, value103, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (409 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value94, value102, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (411 : Vertex) (395 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value102, value107, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (411 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 231 = true ∨ valuation q 94 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value94, value103, value104, value107, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(395 : Vertex), (410 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (409 : Vertex) [(395 : Vertex), (410 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 231 = true ∨ valuation q 94 = true ∨ valuation q 102 = true ∨ valuation q 107 = true := by
  rw [value94, value102, value104, value107, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(395 : Vertex), (409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (410 : Vertex) [(395 : Vertex), (409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 95 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value95, value99, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 95 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value95, value99, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (405 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 95 = false ∨ valuation q 99 = false ∨ valuation q 126 = false := by
  rw [value95, value99, value105, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (405 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 95 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value95, value102, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 95 = false ∨ valuation q 102 = false ∨ valuation q 126 = false := by
  rw [value95, value102, value105, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (409 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 95 = false ∨ valuation q 107 = false ∨ valuation q 126 = false := by
  rw [value95, value105, value107, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (415 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value99, value102, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (405 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 126 = false := by
  rw [value99, value102, value105, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (405 : Vertex) (409 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 99 = false ∨ valuation q 107 = false ∨ valuation q 126 = false := by
  rw [value99, value105, value107, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (405 : Vertex) (415 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 102 = false ∨ valuation q 107 = false ∨ valuation q 126 = false := by
  rw [value102, value105, value107, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (409 : Vertex) (415 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 232 = true ∨ valuation q 95 = true ∨ valuation q 102 = true ∨ valuation q 107 = true ∨ valuation q 126 = true := by
  rw [value95, value102, value105, value107, value126, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(397 : Vertex), (409 : Vertex), (415 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (405 : Vertex) [(397 : Vertex), (409 : Vertex), (415 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 232 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 107 = true ∨ valuation q 126 = true := by
  rw [value95, value99, value105, value107, value126, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(397 : Vertex), (405 : Vertex), (415 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (409 : Vertex) [(397 : Vertex), (405 : Vertex), (415 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 232 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 107 = true := by
  rw [value95, value99, value102, value105, value107, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(397 : Vertex), (405 : Vertex), (409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (477 : Vertex) [(397 : Vertex), (405 : Vertex), (409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 65 = false ∨ valuation q 96 = false := by
  rw [value30, value65, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 65 = false ∨ valuation q 100 = false := by
  rw [value30, value65, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 65 = false ∨ valuation q 103 = false := by
  rw [value30, value65, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 65 = false ∨ valuation q 107 = false := by
  rw [value30, value65, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 30 = false ∨ valuation q 65 = false ∨ valuation q 127 = false := by
  rw [value30, value65, value106, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (286 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E052.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112052
