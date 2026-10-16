import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value103, value104, value105, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (481 : Vertex) (482 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value103, value104, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value103, value105, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (482 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 81 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value81, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (483 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 81 = false ∨ valuation q 107 = false ∨ valuation q 114 = false := by
  rw [value81, value104, value107, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (485 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value103, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (480 : Vertex) (483 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 114 = false := by
  rw [value103, value104, value107, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (480 : Vertex) (485 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 114 = false := by
  rw [value104, value106, value107, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (483 : Vertex) (485 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 226 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 114 = true := by
  rw [value103, value104, value106, value107, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(480 : Vertex), (483 : Vertex), (485 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (417 : Vertex) [(480 : Vertex), (483 : Vertex), (485 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 226 = true ∨ valuation q 81 = true ∨ valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 114 = true := by
  rw [value81, value104, value106, value107, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(417 : Vertex), (483 : Vertex), (485 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (480 : Vertex) [(417 : Vertex), (483 : Vertex), (485 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 226 = true ∨ valuation q 81 = true ∨ valuation q 103 = true ∨ valuation q 107 = true ∨ valuation q 114 = true := by
  rw [value81, value103, value104, value107, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (485 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (483 : Vertex) [(417 : Vertex), (480 : Vertex), (485 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 226 = true ∨ valuation q 81 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value81, value103, value104, value106, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (483 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (485 : Vertex) [(417 : Vertex), (480 : Vertex), (483 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 226 = true ∨ valuation q 81 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 107 = true := by
  rw [value81, value103, value104, value106, value107, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (483 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (497 : Vertex) [(417 : Vertex), (480 : Vertex), (483 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 82 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value82, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (418 : Vertex) (483 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value103, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (480 : Vertex) (483 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value103, value105, value106, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (480 : Vertex) (483 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 227 = true ∨ valuation q 82 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 115 = true := by
  rw [value82, value103, value105, value106, value108, value115, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(418 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (226 : Vertex) [(418 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 227 = true ∨ valuation q 38 = true ∨ valuation q 82 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 108 = true := by
  rw [value38, value82, value103, value105, value106, value108, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(226 : Vertex), (418 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (498 : Vertex) [(226 : Vertex), (418 : Vertex), (480 : Vertex), (483 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 73 = false ∨ valuation q 104 = false := by
  rw [value39, value73, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 73 = false ∨ valuation q 105 = false := by
  rw [value39, value73, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 73 = false ∨ valuation q 110 = false := by
  rw [value39, value73, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 73 = false ∨ valuation q 116 = false := by
  rw [value39, value73, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value39, value104, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (481 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 104 = false ∨ valuation q 110 = false := by
  rw [value39, value104, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (481 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value39, value104, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 105 = false ∨ valuation q 110 = false := by
  rw [value39, value105, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value39, value105, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 39 = false ∨ valuation q 110 = false ∨ valuation q 116 = false := by
  rw [value39, value106, value110, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 73 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value73, value104, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (481 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 73 = false ∨ valuation q 104 = false ∨ valuation q 110 = false := by
  rw [value73, value104, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (481 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 73 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value73, value104, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 73 = false ∨ valuation q 105 = false ∨ valuation q 110 = false := by
  rw [value73, value105, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.First112
