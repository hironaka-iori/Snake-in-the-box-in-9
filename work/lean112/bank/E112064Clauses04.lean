import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 29 = false ∨ valuation q 33 = false ∨ valuation q 103 = false := by
  rw [value29, value32, value33, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 29 = false ∨ valuation q 35 = false ∨ valuation q 103 = false := by
  rw [value29, value32, value35, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (205 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 103 = false := by
  rw [value32, value33, value35, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 150 = true ∨ valuation q 32 = true ∨ valuation q 36 = true := by
  rw [value32, value33, value36, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(197 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (195 : Vertex) [(197 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 150 = true ∨ valuation q 31 = true ∨ valuation q 36 = true := by
  rw [value31, value33, value36, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(195 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (197 : Vertex) [(195 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 150 = true ∨ valuation q 31 = true ∨ valuation q 32 = true := by
  rw [value31, value32, value33, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(195 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(195 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 151 = true ∨ valuation q 44 = true := by
  rw [value34, value44, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(220 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (205 : Vertex) [(220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 151 = true ∨ valuation q 35 = true := by
  rw [value34, value35, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(205 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (220 : Vertex) [(205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value32, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 152 = true ∨ valuation q 32 = true ∨ valuation q 36 = true := by
  rw [value32, value35, value36, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(197 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (204 : Vertex) [(197 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 152 = true ∨ valuation q 32 = true ∨ valuation q 34 = true := by
  rw [value32, value34, value35, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(197 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (207 : Vertex) [(197 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 46 = false := by
  rw [value33, value35, value36, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value33, value35, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 153 = true ∨ valuation q 35 = true ∨ valuation q 46 = true := by
  rw [value35, value36, value46, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(205 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(205 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 153 = true ∨ valuation q 33 = true ∨ valuation q 46 = true := by
  rw [value33, value36, value46, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(199 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [(199 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 153 = true ∨ valuation q 33 = true ∨ valuation q 35 = true := by
  rw [value33, value35, value36, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (223 : Vertex) → w ∈ [(199 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (223 : Vertex) [(199 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 9 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value9, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 9 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value9, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 9 = false ∨ valuation q 38 = false ∨ valuation q 42 = false := by
  rw [value9, value37, value38, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 9 = false ∨ valuation q 38 = false ∨ valuation q 109 = false := by
  rw [value9, value37, value38, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 9 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value9, value37, value39, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 9 = false ∨ valuation q 39 = false ∨ valuation q 109 = false := by
  rw [value9, value37, value39, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (210 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 9 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value9, value37, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (212 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 9 = false ∨ valuation q 40 = false ∨ valuation q 109 = false := by
  rw [value9, value37, value40, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (212 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value37, value38, value39, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (209 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 109 = false := by
  rw [value37, value38, value40, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (209 : Vertex) (212 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 22 = false ∨ valuation q 29 = false ∨ valuation q 37 = false := by
  rw [value22, value29, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (193 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 22 = false ∨ valuation q 29 = false ∨ valuation q 110 = false := by
  rw [value22, value29, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (193 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 22 = false ∨ valuation q 37 = false ∨ valuation q 110 = false := by
  rw [value22, value37, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (208 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 29 = false ∨ valuation q 37 = false ∨ valuation q 110 = false := by
  rw [value29, value37, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (208 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 22 = false ∨ valuation q 29 = false := by
  rw [value22, value29, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (209 : Vertex) (145 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 155 = true ∨ valuation q 29 = true ∨ valuation q 37 = true ∨ valuation q 110 = true := by
  rw [value29, value37, value38, value110, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(193 : Vertex), (208 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (145 : Vertex) [(193 : Vertex), (208 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E064.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112064
