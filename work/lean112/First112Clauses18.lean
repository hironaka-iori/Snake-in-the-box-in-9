import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 73 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value73, value105, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 73 = false ∨ valuation q 110 = false ∨ valuation q 116 = false := by
  rw [value73, value106, value110, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 110 = false := by
  rw [value104, value105, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value104, value105, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 104 = false ∨ valuation q 110 = false ∨ valuation q 116 = false := by
  rw [value104, value106, value110, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 105 = false ∨ valuation q 110 = false ∨ valuation q 116 = false := by
  rw [value105, value106, value110, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 228 = true ∨ valuation q 39 = true ∨ valuation q 73 = true ∨ valuation q 104 = true ∨ valuation q 105 = true ∨ valuation q 110 = true := by
  rw [value39, value73, value104, value105, value106, value110, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (483 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(227 : Vertex), (355 : Vertex), (481 : Vertex), (482 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (483 : Vertex) (499 : Vertex) [(227 : Vertex), (355 : Vertex), (481 : Vertex), (482 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 41 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value41, value84, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 41 = false ∨ valuation q 84 = false ∨ valuation q 111 = false := by
  rw [value41, value84, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (421 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 41 = false ∨ valuation q 104 = false ∨ valuation q 111 = false := by
  rw [value41, value104, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 84 = false ∨ valuation q 104 = false ∨ valuation q 111 = false := by
  rw [value84, value104, value107, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (421 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 42 = false ∨ valuation q 85 = false ∨ valuation q 105 = false := by
  rw [value42, value85, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 42 = false ∨ valuation q 85 = false ∨ valuation q 117 = false := by
  rw [value42, value85, value108, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 42 = false ∨ valuation q 105 = false ∨ valuation q 117 = false := by
  rw [value42, value105, value108, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (482 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 85 = false ∨ valuation q 105 = false ∨ valuation q 117 = false := by
  rw [value85, value105, value108, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (422 : Vertex) (482 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 87 = false ∨ valuation q 103 = false ∨ valuation q 118 = false := by
  rw [value87, value103, value109, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 231 = true ∨ valuation q 103 = true ∨ valuation q 118 = true := by
  rw [value103, value109, value118, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(480 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (424 : Vertex) [(480 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 231 = true ∨ valuation q 87 = true ∨ valuation q 118 = true := by
  rw [value87, value109, value118, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(424 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(424 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 231 = true ∨ valuation q 87 = true ∨ valuation q 103 = true := by
  rw [value87, value103, value109, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (504 : Vertex) [(424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 44 = false ∨ valuation q 89 = false ∨ valuation q 112 = false := by
  rw [value44, value89, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (427 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 44 = false ∨ valuation q 106 = false ∨ valuation q 112 = false := by
  rw [value44, value106, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (483 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 232 = true ∨ valuation q 89 = true ∨ valuation q 106 = true ∨ valuation q 112 = true := by
  rw [value89, value106, value110, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(427 : Vertex), (483 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (235 : Vertex) [(427 : Vertex), (483 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 232 = true ∨ valuation q 44 = true ∨ valuation q 106 = true ∨ valuation q 112 = true := by
  rw [value44, value106, value110, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(235 : Vertex), (483 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (427 : Vertex) [(235 : Vertex), (483 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 232 = true ∨ valuation q 44 = true ∨ valuation q 89 = true ∨ valuation q 112 = true := by
  rw [value44, value89, value110, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(235 : Vertex), (427 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (483 : Vertex) [(235 : Vertex), (427 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 232 = true ∨ valuation q 44 = true ∨ valuation q 89 = true ∨ valuation q 106 = true := by
  rw [value44, value89, value106, value110, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(235 : Vertex), (427 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (495 : Vertex) [(235 : Vertex), (427 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 107 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value107, value111, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (485 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 233 = true ∨ valuation q 112 = true ∨ valuation q 120 = true := by
  rw [value111, value112, value120, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(495 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (485 : Vertex) [(495 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 233 = true ∨ valuation q 107 = true ∨ valuation q 120 = true := by
  rw [value107, value111, value120, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(485 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (495 : Vertex) [(485 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 233 = true ∨ valuation q 107 = true ∨ valuation q 112 = true := by
  rw [value107, value111, value112, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(485 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (509 : Vertex) [(485 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 92 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value92, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 92 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value92, value110, value112, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (491 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 92 = false ∨ valuation q 111 = false ∨ valuation q 122 = false := by
  rw [value92, value111, value112, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (493 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.First112
