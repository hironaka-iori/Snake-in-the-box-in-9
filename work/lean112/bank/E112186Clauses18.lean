import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value87, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 107 = false ∨ valuation q 119 = false := by
  rw [value87, value107, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value87, value109, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (454 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value107, value109, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (454 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 69 = false ∨ valuation q 105 = false := by
  rw [value34, value69, value105, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 69 = false ∨ valuation q 112 = false := by
  rw [value34, value69, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 69 = false ∨ valuation q 113 = false := by
  rw [value34, value69, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 69 = false ∨ valuation q 114 = false := by
  rw [value34, value69, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 105 = false ∨ valuation q 112 = false := by
  rw [value34, value105, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (448 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value34, value105, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (448 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 105 = false ∨ valuation q 114 = false := by
  rw [value34, value105, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value34, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value34, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (457 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 34 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value34, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 69 = false ∨ valuation q 105 = false ∨ valuation q 112 = false := by
  rw [value69, value105, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (448 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 69 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value69, value105, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (448 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 69 = false ∨ valuation q 105 = false ∨ valuation q 114 = false := by
  rw [value69, value105, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 69 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value69, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 69 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value69, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (457 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 69 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value69, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 105 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value105, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (448 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 105 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value105, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (448 : Vertex) (457 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 105 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value105, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (448 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value111, value112, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (457 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 88 = false ∨ valuation q 111 = false ∨ valuation q 120 = false := by
  rw [value88, value111, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (456 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 88 = true ∨ valuation q 111 = true ∨ valuation q 120 = true := by
  rw [value88, value111, value112, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(393 : Vertex), (456 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (201 : Vertex) [(393 : Vertex), (456 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 35 = true ∨ valuation q 111 = true ∨ valuation q 120 = true := by
  rw [value35, value111, value112, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(201 : Vertex), (456 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (393 : Vertex) [(201 : Vertex), (456 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 35 = true ∨ valuation q 88 = true ∨ valuation q 120 = true := by
  rw [value35, value88, value112, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(201 : Vertex), (393 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (456 : Vertex) [(201 : Vertex), (393 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 35 = true ∨ valuation q 88 = true ∨ valuation q 111 = true := by
  rw [value35, value88, value111, value112, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(201 : Vertex), (393 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (473 : Vertex) [(201 : Vertex), (393 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 89 = false ∨ valuation q 106 = false ∨ valuation q 121 = false := by
  rw [value89, value106, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (394 : Vertex) (450 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 89 = false ∨ valuation q 111 = false ∨ valuation q 121 = false := by
  rw [value89, value111, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (394 : Vertex) (456 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 89 = false ∨ valuation q 115 = false ∨ valuation q 121 = false := by
  rw [value89, value113, value115, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (394 : Vertex) (462 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E186.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112186
