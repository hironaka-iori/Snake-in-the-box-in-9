import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 80 = false ∨ valuation q 96 = false ∨ valuation q 118 = false := by
  rw [value80, value96, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (436 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 80 = false ∨ valuation q 96 = false ∨ valuation q 121 = false := by
  rw [value80, value96, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (436 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 80 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value80, value113, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (496 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 80 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value80, value113, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 80 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value80, value117, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value96, value113, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (436 : Vertex) (496 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value96, value113, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (436 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value96, value117, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (436 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 113 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value113, value117, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (496 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 64 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value64, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (246 : Vertex) (498 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 64 = false ∨ valuation q 115 = false ∨ valuation q 123 = false := by
  rw [value64, value115, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (246 : Vertex) (498 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 123 = true := by
  rw [value115, value117, value118, value123, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(498 : Vertex), (500 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (246 : Vertex) [(498 : Vertex), (500 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 64 = true ∨ valuation q 117 = true ∨ valuation q 123 = true := by
  rw [value64, value117, value118, value123, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(246 : Vertex), (500 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (498 : Vertex) [(246 : Vertex), (500 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 64 = true ∨ valuation q 115 = true ∨ valuation q 123 = true := by
  rw [value64, value115, value118, value123, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(246 : Vertex), (498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (500 : Vertex) [(246 : Vertex), (498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 64 = true ∨ valuation q 115 = true ∨ valuation q 117 = true := by
  rw [value64, value115, value117, value118, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(246 : Vertex), (498 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (510 : Vertex) [(246 : Vertex), (498 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 66 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value66, value107, value113, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 66 = false ∨ valuation q 107 = false ∨ valuation q 121 = false := by
  rw [value66, value107, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (488 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 66 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value66, value113, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value107, value113, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (488 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 66 = false ∨ valuation q 113 = false := by
  rw [value66, value113, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (504 : Vertex) (248 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 66 = false ∨ valuation q 121 = false := by
  rw [value66, value121, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (504 : Vertex) (248 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 107 = true ∨ valuation q 113 = true ∨ valuation q 121 = true := by
  rw [value107, value113, value119, value121, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (504 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(488 : Vertex), (496 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (504 : Vertex) (248 : Vertex) [(488 : Vertex), (496 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 66 = true ∨ valuation q 107 = true ∨ valuation q 121 = true := by
  rw [value66, value107, value119, value121, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (504 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(248 : Vertex), (488 : Vertex), (508 : Vertex)] := by decide
  have hg := other_cover q (504 : Vertex) (496 : Vertex) [(248 : Vertex), (488 : Vertex), (508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 66 = true ∨ valuation q 107 = true ∨ valuation q 113 = true := by
  rw [value66, value107, value113, value119, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (504 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(248 : Vertex), (488 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (504 : Vertex) (508 : Vertex) [(248 : Vertex), (488 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 83 = false ∨ valuation q 99 = false := by
  rw [value68, value83, value99, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (379 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 83 = false ∨ valuation q 109 = false := by
  rw [value68, value83, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (379 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 83 = false ∨ valuation q 116 = false := by
  rw [value68, value83, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (379 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 83 = false ∨ valuation q 124 = false := by
  rw [value68, value83, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (379 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value68, value99, value109, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 99 = false ∨ valuation q 116 = false := by
  rw [value68, value99, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 99 = false ∨ valuation q 124 = false := by
  rw [value68, value99, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (443 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 68 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value68, value109, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (251 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E020.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112020
