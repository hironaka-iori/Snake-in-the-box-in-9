import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 133 = true ∨ valuation q 10 = true ∨ valuation q 21 = true ∨ valuation q 60 = true := by
  rw [value10, value19, value21, value60, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(73 : Vertex), (91 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (88 : Vertex) [(73 : Vertex), (91 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value11, value18, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (88 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 61 = false := by
  rw [value11, value18, value20, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (88 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 77 = false := by
  rw [value11, value18, value20, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (88 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 11 = false ∨ valuation q 21 = false ∨ valuation q 61 = false := by
  rw [value11, value20, value21, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (91 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 11 = false ∨ valuation q 21 = false ∨ valuation q 77 = false := by
  rw [value11, value20, value21, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (91 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 11 = false ∨ valuation q 61 = false ∨ valuation q 77 = false := by
  rw [value11, value20, value61, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 61 = false := by
  rw [value18, value20, value21, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 77 = false := by
  rw [value18, value20, value21, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 61 = false ∨ valuation q 77 = false := by
  rw [value18, value20, value61, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 61 = false ∨ valuation q 77 = false := by
  rw [value20, value21, value61, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (91 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value18, value21, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value19, value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (89 : Vertex) (90 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 135 = true ∨ valuation q 20 = true ∨ valuation q 22 = true := by
  rw [value20, value21, value22, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(90 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (89 : Vertex) [(90 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 135 = true ∨ valuation q 19 = true ∨ valuation q 20 = true := by
  rw [value19, value20, value21, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(89 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (95 : Vertex) [(89 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value17, value21, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (95 : Vertex) (87 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 136 = true ∨ valuation q 21 = true := by
  rw [value21, value22, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (87 : Vertex) [(91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 136 = true ∨ valuation q 17 = true := by
  rw [value17, value22, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (91 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 30 = false := by
  rw [value23, value24, value26, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (134 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 44 = false := by
  rw [value23, value24, value26, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (134 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 44 = false := by
  rw [value23, value24, value30, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (138 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 44 = false := by
  rw [value23, value26, value30, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (134 : Vertex) (138 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 24 = false ∨ valuation q 44 = false := by
  rw [value24, value44, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (130 : Vertex) (131 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 137 = true ∨ valuation q 26 = true ∨ valuation q 30 = true ∨ valuation q 44 = true := by
  rw [value23, value26, value30, value44, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(134 : Vertex), (138 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (131 : Vertex) [(134 : Vertex), (138 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 137 = true ∨ valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 44 = true := by
  rw [value23, value24, value26, value44, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(131 : Vertex), (134 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (138 : Vertex) [(131 : Vertex), (134 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 138 = true ∨ valuation q 27 = true ∨ valuation q 45 = true := by
  rw [value24, value27, value45, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(135 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(135 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 138 = true ∨ valuation q 23 = true ∨ valuation q 45 = true := by
  rw [value23, value24, value45, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(130 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(130 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 138 = true ∨ valuation q 23 = true ∨ valuation q 27 = true := by
  rw [value23, value24, value27, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(130 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (195 : Vertex) [(130 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 34 = false := by
  rw [value25, value26, value31, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (134 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 31 = false ∨ valuation q 34 = false := by
  rw [value31, value34, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (132 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 139 = true ∨ valuation q 26 = true ∨ valuation q 34 = true := by
  rw [value25, value26, value34, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(134 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (140 : Vertex) [(134 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 140 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 32 = true := by
  rw [value25, value26, value27, value32, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(132 : Vertex), (135 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (130 : Vertex) [(132 : Vertex), (135 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E168.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112168
