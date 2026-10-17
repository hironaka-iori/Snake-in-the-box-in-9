import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 103 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value103, value105, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value104, value105, value106, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 116 = false := by
  rw [value104, value105, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 104 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value104, value105, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value105, value106, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (487 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 229 = true ∨ valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 109 = true ∨ valuation q 116 = true := by
  rw [value103, value104, value105, value109, value116, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (483 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(481 : Vertex), (482 : Vertex), (491 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (483 : Vertex) (487 : Vertex) [(481 : Vertex), (482 : Vertex), (491 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 89 = false ∨ valuation q 105 = false ∨ valuation q 112 = false := by
  rw [value89, value105, value106, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (483 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 105 = true ∨ valuation q 112 = true := by
  rw [value105, value106, value112, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(483 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (423 : Vertex) [(483 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 89 = true ∨ valuation q 112 = true := by
  rw [value89, value106, value112, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(423 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (483 : Vertex) [(423 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 89 = true ∨ valuation q 105 = true := by
  rw [value89, value105, value106, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(423 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(423 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 55 = false ∨ valuation q 74 = false ∨ valuation q 90 = false := by
  rw [value55, value74, value90, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (360 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 55 = false ∨ valuation q 90 = false ∨ valuation q 102 = false := by
  rw [value55, value90, value102, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 55 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value55, value90, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (424 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 55 = false ∨ valuation q 90 = false ∨ valuation q 119 = false := by
  rw [value55, value90, value107, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (424 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 55 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value55, value102, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (480 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 55 = false ∨ valuation q 102 = false ∨ valuation q 110 = false := by
  rw [value55, value102, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (480 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 55 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value55, value107, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 74 = false ∨ valuation q 90 = false ∨ valuation q 119 = false := by
  rw [value74, value90, value107, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (424 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 74 = false ∨ valuation q 102 = false ∨ valuation q 110 = false := by
  rw [value74, value102, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (480 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 74 = false ∨ valuation q 108 = false ∨ valuation q 119 = false := by
  rw [value74, value107, value108, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (489 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 102 = false ∨ valuation q 110 = false := by
  rw [value90, value102, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 108 = false ∨ valuation q 119 = false := by
  rw [value90, value107, value108, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (489 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 90 = false ∨ valuation q 110 = false ∨ valuation q 119 = false := by
  rw [value90, value107, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (492 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 102 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value102, value107, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (480 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 102 = false ∨ valuation q 108 = false ∨ valuation q 119 = false := by
  rw [value102, value107, value108, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (480 : Vertex) (489 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 119 = false := by
  rw [value107, value108, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (489 : Vertex) (492 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value75, value91, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (425 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 107 = false := by
  rw [value75, value91, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (425 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 109 = false := by
  rw [value75, value91, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (425 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 111 = false := by
  rw [value75, value91, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (425 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value75, value103, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 75 = false ∨ valuation q 103 = false ∨ valuation q 109 = false := by
  rw [value75, value103, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (361 : Vertex) (481 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E020.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112020
