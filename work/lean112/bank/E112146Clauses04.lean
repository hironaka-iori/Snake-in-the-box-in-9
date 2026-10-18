import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 144 = true ∨ valuation q 28 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 47 = true ∨ valuation q 85 = true := by
  rw [value28, value30, value32, value34, value47, value85, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(129 : Vertex), (135 : Vertex), (139 : Vertex), (195 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(129 : Vertex), (135 : Vertex), (139 : Vertex), (195 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 32 = true ∨ valuation q 36 = true := by
  rw [value31, value32, value36, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(135 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (129 : Vertex) [(135 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 28 = true ∨ valuation q 36 = true := by
  rw [value28, value31, value36, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (135 : Vertex) [(129 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 28 = true ∨ valuation q 32 = true := by
  rw [value28, value31, value32, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(129 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (141 : Vertex) [(129 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 37 = false := by
  rw [value30, value31, value32, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 146 = true ∨ valuation q 30 = true ∨ valuation q 37 = true := by
  rw [value30, value32, value37, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(131 : Vertex), (143 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (133 : Vertex) [(131 : Vertex), (143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 147 = true ∨ valuation q 34 = true ∨ valuation q 36 = true := by
  rw [value33, value34, value36, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (129 : Vertex) [(139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 147 = true ∨ valuation q 28 = true ∨ valuation q 36 = true := by
  rw [value28, value33, value36, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (139 : Vertex) [(129 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 147 = true ∨ valuation q 28 = true ∨ valuation q 34 = true := by
  rw [value28, value33, value34, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(129 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (141 : Vertex) [(129 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value2, value30, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (131 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 30 = false ∨ valuation q 37 = false := by
  rw [value2, value30, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (131 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 30 = false ∨ valuation q 51 = false := by
  rw [value2, value30, value34, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (131 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value2, value33, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (137 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 33 = false ∨ valuation q 51 = false := by
  rw [value2, value33, value34, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (137 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 37 = false ∨ valuation q 51 = false := by
  rw [value2, value34, value37, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value30, value33, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 51 = false := by
  rw [value30, value33, value34, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 30 = false ∨ valuation q 37 = false ∨ valuation q 51 = false := by
  rw [value30, value34, value37, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 51 = false := by
  rw [value33, value34, value37, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 148 = true ∨ valuation q 2 = true ∨ valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 37 = true := by
  rw [value2, value30, value33, value34, value37, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(11 : Vertex), (131 : Vertex), (137 : Vertex), (143 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (203 : Vertex) [(11 : Vertex), (131 : Vertex), (137 : Vertex), (143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 52 = false := by
  rw [value35, value36, value42, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (141 : Vertex) (156 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 149 = true ∨ valuation q 42 = true ∨ valuation q 52 = true := by
  rw [value35, value42, value52, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(156 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (141 : Vertex) [(156 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 149 = true ∨ valuation q 36 = true ∨ valuation q 52 = true := by
  rw [value35, value36, value52, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(141 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (156 : Vertex) [(141 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 149 = true ∨ valuation q 36 = true ∨ valuation q 42 = true := by
  rw [value35, value36, value42, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(141 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (204 : Vertex) [(141 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 3 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value3, value31, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 3 = false ∨ valuation q 31 = false ∨ valuation q 35 = false := by
  rw [value3, value31, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 3 = false ∨ valuation q 31 = false ∨ valuation q 37 = false := by
  rw [value3, value31, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 3 = false ∨ valuation q 31 = false ∨ valuation q 53 = false := by
  rw [value3, value31, value36, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 3 = false ∨ valuation q 31 = false ∨ valuation q 88 = false := by
  rw [value3, value31, value36, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value3, value33, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (137 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value3, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (137 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 53 = false := by
  rw [value3, value33, value36, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (137 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E146.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112146
