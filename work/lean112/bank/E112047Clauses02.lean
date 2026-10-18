import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 25 = false := by
  rw [value15, value17, value20, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 34 = false := by
  rw [value15, value17, value20, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 34 = false := by
  rw [value15, value17, value25, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (145 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 20 = false ∨ valuation q 25 = false ∨ valuation q 34 = false := by
  rw [value15, value20, value25, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (137 : Vertex) (145 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value14, value16, value17, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (128 : Vertex) (131 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 26 = false := by
  rw [value14, value16, value17, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (128 : Vertex) (131 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 80 = false := by
  rw [value14, value16, value17, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (128 : Vertex) (131 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value14, value16, value21, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (128 : Vertex) (138 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 80 = false := by
  rw [value14, value16, value21, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (128 : Vertex) (138 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 26 = false ∨ valuation q 80 = false := by
  rw [value14, value16, value26, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (128 : Vertex) (146 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value16, value17, value21, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (138 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 80 = false := by
  rw [value16, value17, value21, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (138 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 80 = false := by
  rw [value16, value17, value26, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 80 = false := by
  rw [value16, value21, value26, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (138 : Vertex) (146 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 134 = true ∨ valuation q 14 = true ∨ valuation q 21 = true ∨ valuation q 26 = true ∨ valuation q 80 = true := by
  rw [value14, value16, value21, value26, value80, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(128 : Vertex), (138 : Vertex), (146 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (131 : Vertex) [(128 : Vertex), (138 : Vertex), (146 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 134 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 26 = true ∨ valuation q 80 = true := by
  rw [value14, value16, value17, value26, value80, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(128 : Vertex), (131 : Vertex), (146 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (138 : Vertex) [(128 : Vertex), (131 : Vertex), (146 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 134 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 21 = true ∨ valuation q 80 = true := by
  rw [value14, value16, value17, value21, value80, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(128 : Vertex), (131 : Vertex), (138 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (146 : Vertex) [(128 : Vertex), (131 : Vertex), (138 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 134 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 21 = true ∨ valuation q 26 = true := by
  rw [value14, value16, value17, value21, value26, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(128 : Vertex), (131 : Vertex), (138 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (386 : Vertex) [(128 : Vertex), (131 : Vertex), (138 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 27 = true ∨ valuation q 81 = true := by
  rw [value15, value16, value17, value19, value27, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ∈ [(129 : Vertex), (130 : Vertex), (135 : Vertex), (147 : Vertex), (387 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (131 : Vertex) [(129 : Vertex), (130 : Vertex), (135 : Vertex), (147 : Vertex), (387 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value15, value16, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (129 : Vertex) (130 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 81 = false := by
  rw [value15, value16, value17, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (129 : Vertex) (130 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 27 = false := by
  rw [value16, value17, value19, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (130 : Vertex) (135 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 81 = false := by
  rw [value16, value17, value27, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (130 : Vertex) (147 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 27 = false ∨ valuation q 81 = false := by
  rw [value17, value19, value27, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (135 : Vertex) (147 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 27 = true ∨ valuation q 81 = true := by
  rw [value15, value17, value19, value27, value81, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(129 : Vertex), (135 : Vertex), (147 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(129 : Vertex), (135 : Vertex), (147 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 27 = true ∨ valuation q 81 = true := by
  rw [value15, value16, value17, value27, value81, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(129 : Vertex), (130 : Vertex), (147 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(129 : Vertex), (130 : Vertex), (147 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 81 = true := by
  rw [value15, value16, value17, value19, value81, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(129 : Vertex), (130 : Vertex), (135 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (147 : Vertex) [(129 : Vertex), (130 : Vertex), (135 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 27 = true := by
  rw [value15, value16, value17, value19, value27, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(129 : Vertex), (130 : Vertex), (135 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (387 : Vertex) [(129 : Vertex), (130 : Vertex), (135 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 14 = false ∨ valuation q 28 = false ∨ valuation q 82 = false := by
  rw [value14, value18, value28, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (128 : Vertex) (148 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 136 = true ∨ valuation q 14 = true ∨ valuation q 82 = true := by
  rw [value14, value18, value82, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(128 : Vertex), (388 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (148 : Vertex) [(128 : Vertex), (388 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 23 = false ∨ valuation q 36 = false := by
  rw [value17, value19, value23, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 23 = false ∨ valuation q 84 = false := by
  rw [value17, value19, value23, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E047.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112047
