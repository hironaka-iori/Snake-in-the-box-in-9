import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 84 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value84, value106, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 84 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value84, value106, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 84 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value84, value106, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (454 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value105, value106, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (448 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value105, value106, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (448 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value105, value106, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (448 : Vertex) (454 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value106, value107, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (451 : Vertex) (454 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 67 = false ∨ valuation q 85 = false ∨ valuation q 106 = false := by
  rw [value67, value85, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (387 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 67 = false ∨ valuation q 85 = false ∨ valuation q 110 = false := by
  rw [value67, value85, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (387 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 67 = false ∨ valuation q 106 = false ∨ valuation q 110 = false := by
  rw [value67, value106, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (450 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 85 = false ∨ valuation q 106 = false ∨ valuation q 110 = false := by
  rw [value85, value106, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (387 : Vertex) (450 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 85 = true ∨ valuation q 106 = true ∨ valuation q 110 = true := by
  rw [value85, value106, value107, value110, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(387 : Vertex), (450 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (323 : Vertex) [(387 : Vertex), (450 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 67 = true ∨ valuation q 106 = true ∨ valuation q 110 = true := by
  rw [value67, value106, value107, value110, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(323 : Vertex), (450 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (387 : Vertex) [(323 : Vertex), (450 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 67 = true ∨ valuation q 85 = true ∨ valuation q 110 = true := by
  rw [value67, value85, value107, value110, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(323 : Vertex), (387 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(323 : Vertex), (387 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 67 = true ∨ valuation q 85 = true ∨ valuation q 106 = true := by
  rw [value67, value85, value106, value107, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(323 : Vertex), (387 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (455 : Vertex) [(323 : Vertex), (387 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value105, value108, value109, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (448 : Vertex) (454 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 117 = false := by
  rw [value105, value108, value109, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (448 : Vertex) (454 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 105 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value105, value108, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (448 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value108, value109, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (454 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value106, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (450 : Vertex) (452 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 115 = false := by
  rw [value106, value108, value109, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (450 : Vertex) (452 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value108, value109, value110, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (452 : Vertex) (455 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 115 = true := by
  rw [value108, value109, value110, value115, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(452 : Vertex), (455 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (450 : Vertex) [(452 : Vertex), (455 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 106 = true ∨ valuation q 110 = true ∨ valuation q 115 = true := by
  rw [value106, value109, value110, value115, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(450 : Vertex), (455 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (452 : Vertex) [(450 : Vertex), (455 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 115 = true := by
  rw [value106, value108, value109, value115, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(450 : Vertex), (452 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (455 : Vertex) [(450 : Vertex), (452 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 233 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 110 = true := by
  rw [value106, value108, value109, value110, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(450 : Vertex), (452 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (462 : Vertex) [(450 : Vertex), (452 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 33 = false ∨ valuation q 87 = false ∨ valuation q 107 = false := by
  rw [value33, value87, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 33 = false ∨ valuation q 87 = false ∨ valuation q 109 = false := by
  rw [value33, value87, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 33 = false ∨ valuation q 87 = false ∨ valuation q 119 = false := by
  rw [value33, value87, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 33 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value33, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 33 = false ∨ valuation q 107 = false ∨ valuation q 119 = false := by
  rw [value33, value107, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 33 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value33, value109, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (454 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E186.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112186
