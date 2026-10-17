import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 152 = true ∨ valuation q 25 = true := by
  rw [value24, value25, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(146 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (152 : Vertex) [(146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value15, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (144 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 153 = true ∨ valuation q 24 = true ∨ valuation q 26 = true := by
  rw [value24, value25, value26, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(144 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (130 : Vertex) [(144 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 153 = true ∨ valuation q 15 = true ∨ valuation q 26 = true := by
  rw [value15, value25, value26, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(130 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (144 : Vertex) [(130 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 153 = true ∨ valuation q 15 = true ∨ valuation q 24 = true := by
  rw [value15, value24, value25, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(130 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (147 : Vertex) [(130 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 27 = false := by
  rw [value16, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (146 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 16 = false ∨ valuation q 25 = false := by
  rw [value16, value25, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (147 : Vertex) (131 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 154 = true ∨ valuation q 25 = true ∨ valuation q 27 = true := by
  rw [value25, value26, value27, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(146 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (131 : Vertex) [(146 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 154 = true ∨ valuation q 16 = true ∨ valuation q 27 = true := by
  rw [value16, value26, value27, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(131 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (146 : Vertex) [(131 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 31 = false ∨ valuation q 44 = false ∨ valuation q 102 = false := by
  rw [value27, value31, value44, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (159 : Vertex) (215 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 155 = true ∨ valuation q 31 = true ∨ valuation q 44 = true ∨ valuation q 102 = true := by
  rw [value27, value31, value44, value102, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(159 : Vertex), (215 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (147 : Vertex) [(159 : Vertex), (215 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 155 = true ∨ valuation q 26 = true ∨ valuation q 44 = true ∨ valuation q 102 = true := by
  rw [value26, value27, value44, value102, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(147 : Vertex), (215 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (159 : Vertex) [(147 : Vertex), (215 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 155 = true ∨ valuation q 26 = true ∨ valuation q 31 = true ∨ valuation q 102 = true := by
  rw [value26, value27, value31, value102, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(147 : Vertex), (159 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (215 : Vertex) [(147 : Vertex), (159 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 155 = true ∨ valuation q 26 = true ∨ valuation q 31 = true ∨ valuation q 44 = true := by
  rw [value26, value27, value31, value44, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(147 : Vertex), (159 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (407 : Vertex) [(147 : Vertex), (159 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 156 = true ∨ valuation q 29 = true := by
  rw [value28, value29, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(156 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (144 : Vertex) [(156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 156 = true ∨ valuation q 24 = true := by
  rw [value24, value28, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (156 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value21, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (140 : Vertex) (152 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 157 = true ∨ valuation q 21 = true ∨ valuation q 30 = true := by
  rw [value21, value29, value30, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(140 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (152 : Vertex) [(140 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value23, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (142 : Vertex) (156 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 107 = false := by
  rw [value29, value30, value31, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (156 : Vertex) (159 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 158 = true ∨ valuation q 23 = true ∨ valuation q 31 = true ∨ valuation q 107 = true := by
  rw [value23, value30, value31, value107, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(142 : Vertex), (159 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (156 : Vertex) [(142 : Vertex), (159 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 27 = true ∨ valuation q 30 = true ∨ valuation q 108 = true := by
  rw [value27, value30, value31, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ∈ [(151 : Vertex), (158 : Vertex), (415 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (159 : Vertex) [(151 : Vertex), (158 : Vertex), (415 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 108 = false := by
  rw [value27, value30, value31, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (151 : Vertex) (158 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value27, value30, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (159 : Vertex) (151 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 27 = false ∨ valuation q 108 = false := by
  rw [value27, value108, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (159 : Vertex) (151 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 159 = true ∨ valuation q 30 = true ∨ valuation q 108 = true := by
  rw [value30, value31, value108, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(158 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (151 : Vertex) [(158 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 159 = true ∨ valuation q 27 = true ∨ valuation q 108 = true := by
  rw [value27, value31, value108, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(151 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(151 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 109 = false := by
  rw [value32, value33, value36, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 33 = true ∨ valuation q 109 = true := by
  rw [value32, value33, value109, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(194 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(194 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 2 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value2, value32, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (192 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 2 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value2, value33, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (198 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 15 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value15, value32, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (192 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E050.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112050
