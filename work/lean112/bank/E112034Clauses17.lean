import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 32 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value32, value106, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (226 : Vertex) (480 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 32 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value32, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (226 : Vertex) (483 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 32 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value32, value107, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (226 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 69 = false ∨ valuation q 88 = false ∨ valuation q 106 = false := by
  rw [value69, value88, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (354 : Vertex) (418 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 69 = false ∨ valuation q 88 = false ∨ valuation q 108 = false := by
  rw [value69, value88, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (354 : Vertex) (418 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 69 = false ∨ valuation q 88 = false ∨ valuation q 111 = false := by
  rw [value69, value88, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (354 : Vertex) (418 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 69 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value69, value106, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (354 : Vertex) (480 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 69 = false ∨ valuation q 108 = false ∨ valuation q 115 = false := by
  rw [value69, value107, value108, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (354 : Vertex) (483 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 69 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value69, value107, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (354 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 88 = false ∨ valuation q 108 = false ∨ valuation q 115 = false := by
  rw [value88, value107, value108, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (418 : Vertex) (483 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value106, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (480 : Vertex) (483 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value107, value108, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (483 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 235 = true ∨ valuation q 69 = true ∨ valuation q 88 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value69, value88, value106, value107, value108, value111, value115, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(354 : Vertex), (418 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (226 : Vertex) [(354 : Vertex), (418 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 235 = true ∨ valuation q 32 = true ∨ valuation q 88 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value32, value88, value106, value107, value108, value111, value115, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(226 : Vertex), (418 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (354 : Vertex) [(226 : Vertex), (418 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 235 = true ∨ valuation q 32 = true ∨ valuation q 69 = true ∨ valuation q 88 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 115 = true := by
  rw [value32, value69, value88, value106, value107, value108, value115, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(226 : Vertex), (354 : Vertex), (418 : Vertex), (480 : Vertex), (483 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (486 : Vertex) [(226 : Vertex), (354 : Vertex), (418 : Vertex), (480 : Vertex), (483 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 70 = false ∨ valuation q 89 = false := by
  rw [value33, value70, value89, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 70 = false ∨ valuation q 107 = false := by
  rw [value33, value70, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 70 = false ∨ valuation q 112 = false := by
  rw [value33, value70, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 70 = false ∨ valuation q 120 = false := by
  rw [value33, value70, value108, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value33, value89, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (419 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 89 = false ∨ valuation q 112 = false := by
  rw [value33, value89, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (419 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 89 = false ∨ valuation q 120 = false := by
  rw [value33, value89, value108, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (419 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value33, value107, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 107 = false ∨ valuation q 120 = false := by
  rw [value33, value107, value108, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 33 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value33, value108, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 70 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value70, value89, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 70 = false ∨ valuation q 89 = false ∨ valuation q 112 = false := by
  rw [value70, value89, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 70 = false ∨ valuation q 89 = false ∨ valuation q 120 = false := by
  rw [value70, value89, value108, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 70 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value70, value107, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 70 = false ∨ valuation q 107 = false ∨ valuation q 120 = false := by
  rw [value70, value107, value108, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 70 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value70, value108, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 89 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value89, value107, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (419 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E034.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112034
