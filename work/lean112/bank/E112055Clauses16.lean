import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 100 = false := by
  rw [value80, value81, value82, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (276 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 118 = false := by
  rw [value80, value81, value82, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (276 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 100 = false := by
  rw [value80, value81, value86, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (280 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 118 = false := by
  rw [value80, value81, value86, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value80, value81, value100, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (336 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 100 = false := by
  rw [value80, value82, value86, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 118 = false := by
  rw [value80, value82, value86, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value80, value82, value100, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (336 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 86 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value80, value86, value100, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (280 : Vertex) (336 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 208 = true ∨ valuation q 82 = true ∨ valuation q 86 = true ∨ valuation q 100 = true ∨ valuation q 118 = true := by
  rw [value80, value82, value86, value100, value118, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(276 : Vertex), (280 : Vertex), (336 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (274 : Vertex) [(276 : Vertex), (280 : Vertex), (336 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 208 = true ∨ valuation q 81 = true ∨ valuation q 86 = true ∨ valuation q 100 = true ∨ valuation q 118 = true := by
  rw [value80, value81, value86, value100, value118, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(274 : Vertex), (280 : Vertex), (336 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(274 : Vertex), (280 : Vertex), (336 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 208 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 100 = true ∨ valuation q 118 = true := by
  rw [value80, value81, value82, value100, value118, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex), (336 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (280 : Vertex) [(274 : Vertex), (276 : Vertex), (336 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 81 = true := by
  rw [value81, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (274 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 11 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value11, value80, value81, value84, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ∈ [(18 : Vertex), (272 : Vertex), (278 : Vertex), (282 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (274 : Vertex) [(18 : Vertex), (272 : Vertex), (278 : Vertex), (282 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 11 = false ∨ valuation q 80 = false ∨ valuation q 88 = false := by
  rw [value11, value80, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (18 : Vertex) (272 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 11 = false ∨ valuation q 84 = false ∨ valuation q 88 = false := by
  rw [value11, value81, value84, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (18 : Vertex) (278 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 88 = false := by
  rw [value80, value81, value84, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (272 : Vertex) (278 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 11 = false ∨ valuation q 80 = false := by
  rw [value11, value80, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (274 : Vertex) (18 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 11 = false ∨ valuation q 88 = false := by
  rw [value11, value88, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (274 : Vertex) (18 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 209 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value80, value81, value84, value88, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(272 : Vertex), (278 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (18 : Vertex) [(272 : Vertex), (278 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 209 = true ∨ valuation q 11 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value11, value81, value84, value88, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(18 : Vertex), (278 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (272 : Vertex) [(18 : Vertex), (278 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 209 = true ∨ valuation q 11 = true ∨ valuation q 80 = true ∨ valuation q 88 = true := by
  rw [value11, value80, value81, value88, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(18 : Vertex), (272 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (278 : Vertex) [(18 : Vertex), (272 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 209 = true ∨ valuation q 11 = true ∨ valuation q 80 = true ∨ valuation q 84 = true := by
  rw [value11, value80, value81, value84, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(18 : Vertex), (272 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (282 : Vertex) [(18 : Vertex), (272 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 82 = true := by
  rw [value82, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (276 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 70 = true ∨ valuation q 80 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 90 = true := by
  rw [value70, value80, value82, value83, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ∈ [(260 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex), (284 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (276 : Vertex) [(260 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex), (284 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 70 = false ∨ valuation q 80 = false ∨ valuation q 90 = false := by
  rw [value70, value80, value82, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (272 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 70 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value70, value82, value83, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (277 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 80 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 90 = true := by
  rw [value80, value82, value83, value84, value90, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(272 : Vertex), (277 : Vertex), (278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (260 : Vertex) [(272 : Vertex), (277 : Vertex), (278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 70 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 90 = true := by
  rw [value70, value82, value83, value84, value90, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(260 : Vertex), (277 : Vertex), (278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(260 : Vertex), (277 : Vertex), (278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 70 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 90 = true := by
  rw [value70, value80, value82, value84, value90, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex), (272 : Vertex), (278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(260 : Vertex), (272 : Vertex), (278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 70 = true ∨ valuation q 80 = true ∨ valuation q 83 = true ∨ valuation q 90 = true := by
  rw [value70, value80, value82, value83, value90, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(260 : Vertex), (272 : Vertex), (277 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (278 : Vertex) [(260 : Vertex), (272 : Vertex), (277 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 210 = true ∨ valuation q 70 = true ∨ valuation q 80 = true ∨ valuation q 83 = true ∨ valuation q 84 = true := by
  rw [value70, value80, value82, value83, value84, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(260 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (284 : Vertex) [(260 : Vertex), (272 : Vertex), (277 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block16 (q : Snake 81) (h : Conditions q) : B112E055.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112055
