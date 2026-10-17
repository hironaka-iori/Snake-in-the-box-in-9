import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 30 = true ∨ valuation q 36 = true := by
  rw [value30, value31, value36, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(129 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(129 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 30 = true ∨ valuation q 34 = true := by
  rw [value30, value31, value34, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(129 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (139 : Vertex) [(129 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 2 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value2, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (133 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 2 = false ∨ valuation q 33 = false ∨ valuation q 49 = false := by
  rw [value2, value32, value33, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (133 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 2 = false ∨ valuation q 37 = false ∨ valuation q 49 = false := by
  rw [value2, value32, value37, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (140 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 49 = false := by
  rw [value32, value33, value37, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 33 = true ∨ valuation q 37 = true ∨ valuation q 49 = true := by
  rw [value32, value33, value37, value49, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(133 : Vertex), (140 : Vertex), (196 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (4 : Vertex) [(133 : Vertex), (140 : Vertex), (196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 2 = true ∨ valuation q 37 = true ∨ valuation q 49 = true := by
  rw [value2, value32, value37, value49, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(4 : Vertex), (140 : Vertex), (196 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (133 : Vertex) [(4 : Vertex), (140 : Vertex), (196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 2 = true ∨ valuation q 33 = true ∨ valuation q 49 = true := by
  rw [value2, value32, value33, value49, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(4 : Vertex), (133 : Vertex), (196 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (140 : Vertex) [(4 : Vertex), (133 : Vertex), (196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 38 = false := by
  rw [value30, value32, value33, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (132 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 50 = false := by
  rw [value30, value32, value33, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (132 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 38 = false := by
  rw [value30, value33, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (135 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 86 = false := by
  rw [value30, value33, value34, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (135 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 30 = false ∨ valuation q 38 = false ∨ valuation q 50 = false := by
  rw [value30, value33, value38, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (141 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 38 = false := by
  rw [value32, value33, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 50 = false := by
  rw [value32, value33, value34, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 30 = true ∨ valuation q 32 = true ∨ valuation q 38 = true ∨ valuation q 50 = true ∨ valuation q 86 = true := by
  rw [value30, value32, value33, value38, value50, value86, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(129 : Vertex), (132 : Vertex), (141 : Vertex), (197 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (135 : Vertex) [(129 : Vertex), (132 : Vertex), (141 : Vertex), (197 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 30 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 38 = true ∨ valuation q 50 = true := by
  rw [value30, value32, value33, value34, value38, value50, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(129 : Vertex), (132 : Vertex), (135 : Vertex), (141 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (389 : Vertex) [(129 : Vertex), (132 : Vertex), (135 : Vertex), (141 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 4 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value4, value31, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (7 : Vertex) (131 : Vertex) (133 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 4 = false ∨ valuation q 31 = false ∨ valuation q 88 = false := by
  rw [value4, value31, value34, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (7 : Vertex) (131 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 88 = false := by
  rw [value31, value33, value34, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 5 = false ∨ valuation q 30 = false ∨ valuation q 38 = false := by
  rw [value5, value30, value35, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (129 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 30 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value30, value35, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (139 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 30 = false ∨ valuation q 38 = false ∨ valuation q 90 = false := by
  rw [value30, value35, value38, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (141 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 54 = false := by
  rw [value31, value35, value36, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 160 = true ∨ valuation q 35 = true ∨ valuation q 54 = true := by
  rw [value35, value36, value54, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(137 : Vertex), (203 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (131 : Vertex) [(137 : Vertex), (203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 160 = true ∨ valuation q 31 = true ∨ valuation q 35 = true := by
  rw [value31, value35, value36, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(131 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (203 : Vertex) [(131 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 37 = true := by
  rw [value37, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (140 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 32 = true ∨ valuation q 38 = true ∨ valuation q 55 = true := by
  rw [value32, value37, value38, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ∈ [(132 : Vertex), (141 : Vertex), (204 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (140 : Vertex) [(132 : Vertex), (141 : Vertex), (204 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 38 = true ∨ valuation q 55 = true := by
  rw [value37, value38, value55, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(141 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (132 : Vertex) [(141 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 32 = true ∨ valuation q 55 = true := by
  rw [value32, value37, value55, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(132 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (141 : Vertex) [(132 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value32, value37, value38, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(132 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (204 : Vertex) [(132 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E105.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112105
