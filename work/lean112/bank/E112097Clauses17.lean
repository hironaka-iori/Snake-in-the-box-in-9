import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value87, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (489 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 108 = false ∨ valuation q 113 = false := by
  rw [value87, value108, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (489 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 108 = false ∨ valuation q 121 = false := by
  rw [value87, value108, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (489 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value87, value109, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (490 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 109 = false ∨ valuation q 121 = false := by
  rw [value87, value109, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (490 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value87, value110, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (495 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value108, value109, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (489 : Vertex) (490 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 121 = false := by
  rw [value108, value109, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (489 : Vertex) (490 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 108 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value108, value110, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (489 : Vertex) (495 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value109, value110, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (490 : Vertex) (495 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 233 = true ∨ valuation q 87 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 113 = true := by
  rw [value87, value108, value109, value110, value113, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(427 : Vertex), (489 : Vertex), (490 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (507 : Vertex) [(427 : Vertex), (489 : Vertex), (490 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 88 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value88, value107, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (428 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 234 = true ∨ valuation q 104 = true ∨ valuation q 107 = true ∨ valuation q 112 = true := by
  rw [value104, value107, value111, value112, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(484 : Vertex), (488 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (428 : Vertex) [(484 : Vertex), (488 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 234 = true ∨ valuation q 88 = true ∨ valuation q 107 = true ∨ valuation q 112 = true := by
  rw [value88, value107, value111, value112, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (484 : Vertex) → w ∈ [(428 : Vertex), (488 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (484 : Vertex) [(428 : Vertex), (488 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 234 = true ∨ valuation q 88 = true ∨ valuation q 104 = true ∨ valuation q 112 = true := by
  rw [value88, value104, value111, value112, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(428 : Vertex), (484 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (488 : Vertex) [(428 : Vertex), (484 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 234 = true ∨ valuation q 88 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value88, value104, value107, value111, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(428 : Vertex), (484 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (494 : Vertex) [(428 : Vertex), (484 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 72 = false ∨ valuation q 89 = false := by
  rw [value36, value72, value89, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (366 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 72 = false ∨ valuation q 106 = false := by
  rw [value36, value72, value106, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (366 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 72 = false ∨ valuation q 109 = false := by
  rw [value36, value72, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (366 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 72 = false ∨ valuation q 111 = false := by
  rw [value36, value72, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (366 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 72 = false ∨ valuation q 113 = false := by
  rw [value36, value72, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (366 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 89 = false ∨ valuation q 106 = false := by
  rw [value36, value89, value106, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 89 = false ∨ valuation q 109 = false := by
  rw [value36, value89, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (430 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 89 = false ∨ valuation q 111 = false := by
  rw [value36, value89, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (430 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 89 = false ∨ valuation q 113 = false := by
  rw [value36, value89, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value36, value106, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value36, value106, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (486 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 106 = false ∨ valuation q 113 = false := by
  rw [value36, value106, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (486 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value36, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value36, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (490 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 36 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value36, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (238 : Vertex) (492 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 72 = false ∨ valuation q 89 = false ∨ valuation q 106 = false := by
  rw [value72, value89, value106, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (366 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E097.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112097
