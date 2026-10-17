import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 62 = false ∨ valuation q 111 = false := by
  rw [value40, value62, value99, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 79 = false ∨ valuation q 111 = false := by
  rw [value40, value79, value99, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (384 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 100 = false ∨ valuation q 105 = false := by
  rw [value40, value99, value100, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (449 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 100 = false ∨ valuation q 111 = false := by
  rw [value40, value99, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value40, value99, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (450 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 101 = false ∨ valuation q 111 = false := by
  rw [value40, value99, value101, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 62 = false ∨ valuation q 79 = false ∨ valuation q 100 = false := by
  rw [value62, value79, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (384 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 62 = false ∨ valuation q 79 = false ∨ valuation q 111 = false := by
  rw [value62, value79, value99, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (384 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 62 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value62, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (449 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 62 = false ∨ valuation q 100 = false ∨ valuation q 111 = false := by
  rw [value62, value99, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 62 = false ∨ valuation q 101 = false ∨ valuation q 111 = false := by
  rw [value62, value99, value101, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value99, value100, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (449 : Vertex) (450 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 105 = false ∨ valuation q 111 = false := by
  rw [value99, value100, value105, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (449 : Vertex) (456 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 111 = false := by
  rw [value99, value101, value105, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (450 : Vertex) (456 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 62 = true ∨ valuation q 79 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 105 = true ∨ valuation q 111 = true := by
  rw [value62, value79, value99, value100, value101, value105, value111, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(320 : Vertex), (384 : Vertex), (449 : Vertex), (450 : Vertex), (456 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (192 : Vertex) [(320 : Vertex), (384 : Vertex), (449 : Vertex), (450 : Vertex), (456 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 40 = true ∨ valuation q 62 = true ∨ valuation q 79 = true ∨ valuation q 100 = true ∨ valuation q 105 = true ∨ valuation q 111 = true := by
  rw [value40, value62, value79, value99, value100, value105, value111, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(192 : Vertex), (320 : Vertex), (384 : Vertex), (449 : Vertex), (456 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (450 : Vertex) [(192 : Vertex), (320 : Vertex), (384 : Vertex), (449 : Vertex), (456 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 40 = true ∨ valuation q 62 = true ∨ valuation q 79 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 111 = true := by
  rw [value40, value62, value79, value99, value100, value101, value111, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(192 : Vertex), (320 : Vertex), (384 : Vertex), (449 : Vertex), (450 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (456 : Vertex) [(192 : Vertex), (320 : Vertex), (384 : Vertex), (449 : Vertex), (450 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 63 = false ∨ valuation q 80 = false := by
  rw [value41, value63, value80, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 63 = false ∨ valuation q 99 = false := by
  rw [value41, value63, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 63 = false ∨ valuation q 102 = false := by
  rw [value41, value63, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 63 = false ∨ valuation q 103 = false := by
  rw [value41, value63, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 63 = false ∨ valuation q 112 = false := by
  rw [value41, value63, value100, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 80 = false ∨ valuation q 99 = false := by
  rw [value41, value80, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (385 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 80 = false ∨ valuation q 102 = false := by
  rw [value41, value80, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (385 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 80 = false ∨ valuation q 103 = false := by
  rw [value41, value80, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (385 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 80 = false ∨ valuation q 112 = false := by
  rw [value41, value80, value100, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (385 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value41, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 99 = false ∨ valuation q 103 = false := by
  rw [value41, value99, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value41, value99, value100, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (448 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value41, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value41, value100, value102, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 41 = false ∨ valuation q 103 = false ∨ valuation q 112 = false := by
  rw [value41, value100, value103, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E019.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112019
