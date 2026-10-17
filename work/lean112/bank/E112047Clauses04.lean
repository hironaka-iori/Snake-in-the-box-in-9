import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 26 = true := by
  rw [value26, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (146 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 41 = true := by
  rw [value6, value16, value24, value26, value27, value29, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ∈ [(18 : Vertex), (130 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex), (210 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (146 : Vertex) [(18 : Vertex), (130 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex), (210 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 41 = false := by
  rw [value16, value26, value27, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (147 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value24, value26, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (144 : Vertex) (147 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 16 = true ∨ valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 41 = true := by
  rw [value16, value24, value26, value27, value29, value41, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(130 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (18 : Vertex) [(130 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 6 = true ∨ valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 41 = true := by
  rw [value6, value24, value26, value27, value29, value41, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(18 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (130 : Vertex) [(18 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 41 = true := by
  rw [value6, value16, value26, value27, value29, value41, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(18 : Vertex), (130 : Vertex), (147 : Vertex), (154 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (144 : Vertex) [(18 : Vertex), (130 : Vertex), (147 : Vertex), (154 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 24 = true ∨ valuation q 29 = true ∨ valuation q 41 = true := by
  rw [value6, value16, value24, value26, value29, value41, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(18 : Vertex), (130 : Vertex), (144 : Vertex), (154 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (147 : Vertex) [(18 : Vertex), (130 : Vertex), (144 : Vertex), (154 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 41 = true := by
  rw [value6, value16, value24, value26, value27, value41, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(18 : Vertex), (130 : Vertex), (144 : Vertex), (147 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (154 : Vertex) [(18 : Vertex), (130 : Vertex), (144 : Vertex), (147 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 6 = true ∨ valuation q 16 = true ∨ valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value6, value16, value24, value26, value27, value29, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(18 : Vertex), (130 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (210 : Vertex) [(18 : Vertex), (130 : Vertex), (144 : Vertex), (147 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value17, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (145 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 91 = false := by
  rw [value17, value25, value27, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (145 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 91 = false := by
  rw [value17, value26, value27, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (146 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 91 = false := by
  rw [value25, value26, value27, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (145 : Vertex) (146 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 91 = true := by
  rw [value25, value26, value27, value91, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(145 : Vertex), (146 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (131 : Vertex) [(145 : Vertex), (146 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 17 = true ∨ valuation q 26 = true ∨ valuation q 91 = true := by
  rw [value17, value26, value27, value91, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(131 : Vertex), (146 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (145 : Vertex) [(131 : Vertex), (146 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 28 = true := by
  rw [value28, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (148 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 18 = true ∨ valuation q 24 = true ∨ valuation q 30 = true := by
  rw [value18, value24, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ∈ [(132 : Vertex), (144 : Vertex), (156 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (148 : Vertex) [(132 : Vertex), (144 : Vertex), (156 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 24 = true ∨ valuation q 30 = true := by
  rw [value24, value28, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(144 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (132 : Vertex) [(144 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 18 = true ∨ valuation q 30 = true := by
  rw [value18, value28, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(132 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(132 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 18 = true ∨ valuation q 24 = true := by
  rw [value18, value24, value28, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(132 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (156 : Vertex) [(132 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 31 = false := by
  rw [value21, value26, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (146 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 47 = false := by
  rw [value21, value26, value29, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (146 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 97 = false := by
  rw [value21, value26, value29, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (146 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 31 = false ∨ valuation q 47 = false := by
  rw [value21, value29, value31, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (158 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 31 = false ∨ valuation q 97 = false := by
  rw [value21, value29, value31, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (158 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 47 = false ∨ valuation q 97 = false := by
  rw [value21, value29, value47, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (218 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 47 = false := by
  rw [value26, value29, value31, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (146 : Vertex) (158 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 97 = false := by
  rw [value26, value29, value31, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (146 : Vertex) (158 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 26 = false ∨ valuation q 47 = false ∨ valuation q 97 = false := by
  rw [value26, value29, value47, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (146 : Vertex) (218 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 47 = false ∨ valuation q 97 = false := by
  rw [value29, value31, value47, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (158 : Vertex) (218 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 26 = true ∨ valuation q 31 = true ∨ valuation q 47 = true ∨ valuation q 97 = true := by
  rw [value26, value29, value31, value47, value97, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(146 : Vertex), (158 : Vertex), (218 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (138 : Vertex) [(146 : Vertex), (158 : Vertex), (218 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E047.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112047
