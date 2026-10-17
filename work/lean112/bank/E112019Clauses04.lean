import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 151 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(143 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (133 : Vertex) [(143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 151 = true ∨ valuation q 26 = true := by
  rw [value26, value30, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(133 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (143 : Vertex) [(133 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 31 = true := by
  rw [value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (143 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 39 = false := by
  rw [value29, value30, value31, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (139 : Vertex) (141 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 152 = true ∨ valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 39 = true := by
  rw [value29, value30, value31, value39, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(139 : Vertex), (141 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (135 : Vertex) [(139 : Vertex), (141 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 152 = true ∨ valuation q 27 = true ∨ valuation q 30 = true ∨ valuation q 39 = true := by
  rw [value27, value30, value31, value39, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(135 : Vertex), (141 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (139 : Vertex) [(135 : Vertex), (141 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 152 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 39 = true := by
  rw [value27, value29, value31, value39, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (141 : Vertex) [(135 : Vertex), (139 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 152 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value27, value29, value30, value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (159 : Vertex) [(135 : Vertex), (139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value32, value33, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (145 : Vertex) (148 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 153 = true ∨ valuation q 35 = true ∨ valuation q 36 = true := by
  rw [value32, value35, value36, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(148 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (145 : Vertex) [(148 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 153 = true ∨ valuation q 33 = true ∨ valuation q 35 = true := by
  rw [value32, value33, value35, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(145 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (152 : Vertex) [(145 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = true ∨ valuation q 34 = true := by
  rw [value32, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ∈ [(144 : Vertex), (147 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (145 : Vertex) [(144 : Vertex), (147 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 154 = true ∨ valuation q 34 = true := by
  rw [value33, value34, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(147 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (144 : Vertex) [(147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 154 = true ∨ valuation q 32 = true := by
  rw [value32, value33, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (147 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 155 = true ∨ valuation q 33 = true := by
  rw [value33, value34, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(145 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (131 : Vertex) [(145 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 155 = true ∨ valuation q 24 = true := by
  rw [value24, value34, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(131 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (145 : Vertex) [(131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 35 = true := by
  rw [value35, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (148 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 25 = false ∨ valuation q 32 = false ∨ valuation q 37 = false := by
  rw [value25, value32, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (144 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 50 = false := by
  rw [value32, value35, value37, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (144 : Vertex) (156 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 156 = true ∨ valuation q 25 = true ∨ valuation q 37 = true ∨ valuation q 50 = true := by
  rw [value25, value35, value37, value50, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(132 : Vertex), (156 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(132 : Vertex), (156 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 94 = false := by
  rw [value32, value36, value37, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (144 : Vertex) (156 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 37 = true := by
  rw [value32, value36, value37, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(144 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (408 : Vertex) [(144 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value35, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (148 : Vertex) (152 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 158 = true ∨ valuation q 35 = true ∨ valuation q 38 = true := by
  rw [value35, value37, value38, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(148 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (152 : Vertex) [(148 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 158 = true ∨ valuation q 35 = true ∨ valuation q 36 = true := by
  rw [value35, value36, value37, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(148 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (158 : Vertex) [(148 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = true ∨ valuation q 39 = true := by
  rw [value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ∈ [(156 : Vertex), (159 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (158 : Vertex) [(156 : Vertex), (159 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 159 = true ∨ valuation q 39 = true := by
  rw [value38, value39, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (156 : Vertex) [(159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 159 = true ∨ valuation q 37 = true := by
  rw [value37, value38, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(156 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (159 : Vertex) [(156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 31 = false ∨ valuation q 38 = false ∨ valuation q 98 = false := by
  rw [value31, value38, value39, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (143 : Vertex) (158 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 160 = true ∨ valuation q 38 = true ∨ valuation q 98 = true := by
  rw [value38, value39, value98, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(158 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (143 : Vertex) [(158 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 160 = true ∨ valuation q 31 = true ∨ valuation q 98 = true := by
  rw [value31, value39, value98, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(143 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(143 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 99 = false := by
  rw [value40, value41, value44, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E019.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112019
