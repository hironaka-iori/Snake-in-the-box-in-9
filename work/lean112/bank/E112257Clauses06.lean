import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 4 = false ∨ valuation q 40 = false ∨ valuation q 45 = false := by
  rw [value4, value39, value40, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (135 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 4 = false ∨ valuation q 40 = false ∨ valuation q 50 = false := by
  rw [value4, value39, value40, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (135 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 50 = false := by
  rw [value4, value39, value45, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (142 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 60 = false := by
  rw [value4, value39, value45, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (142 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 4 = false ∨ valuation q 50 = false ∨ valuation q 60 = false := by
  rw [value4, value39, value50, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (150 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 45 = false ∨ valuation q 50 = false := by
  rw [value39, value40, value45, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (135 : Vertex) (142 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 45 = false ∨ valuation q 60 = false := by
  rw [value39, value40, value45, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (135 : Vertex) (142 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 50 = false ∨ valuation q 60 = false := by
  rw [value39, value40, value50, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (135 : Vertex) (150 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 60 = false := by
  rw [value39, value45, value50, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (142 : Vertex) (150 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value5, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (7 : Vertex) (131 : Vertex) (133 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value5, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (7 : Vertex) (133 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 39 = true := by
  rw [value37, value38, value39, value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(131 : Vertex), (133 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (7 : Vertex) [(131 : Vertex), (133 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 5 = true ∨ valuation q 38 = true ∨ valuation q 39 = true := by
  rw [value5, value38, value39, value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(7 : Vertex), (133 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (131 : Vertex) [(7 : Vertex), (133 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 5 = true ∨ valuation q 37 = true ∨ valuation q 39 = true := by
  rw [value5, value37, value39, value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(7 : Vertex), (131 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (133 : Vertex) [(7 : Vertex), (131 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 5 = true ∨ valuation q 37 = true ∨ valuation q 38 = true := by
  rw [value5, value37, value38, value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(7 : Vertex), (131 : Vertex), (133 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (134 : Vertex) [(7 : Vertex), (131 : Vertex), (133 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 7 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value7, value41, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (10 : Vertex) (139 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 7 = false ∨ valuation q 42 = false ∨ valuation q 63 = false := by
  rw [value7, value41, value42, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (10 : Vertex) (139 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 7 = false ∨ valuation q 45 = false ∨ valuation q 63 = false := by
  rw [value7, value41, value45, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (10 : Vertex) (142 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 63 = false := by
  rw [value41, value42, value45, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (142 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 157 = true ∨ valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 63 = true := by
  rw [value41, value42, value45, value63, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(139 : Vertex), (142 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (10 : Vertex) [(139 : Vertex), (142 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 53 = false := by
  rw [value37, value41, value42, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 41 = true ∨ valuation q 53 = true := by
  rw [value41, value42, value53, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(138 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (131 : Vertex) [(138 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 37 = true ∨ valuation q 53 = true := by
  rw [value37, value42, value53, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(131 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (138 : Vertex) [(131 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value37, value41, value42, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(131 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (155 : Vertex) [(131 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 54 = false := by
  rw [value43, value44, value45, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (141 : Vertex) (142 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 64 = false := by
  rw [value43, value44, value45, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (141 : Vertex) (142 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value43, value44, value54, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (141 : Vertex) (156 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value43, value45, value54, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (142 : Vertex) (156 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 159 = true ∨ valuation q 44 = true ∨ valuation q 45 = true ∨ valuation q 54 = true := by
  rw [value43, value44, value45, value54, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(141 : Vertex), (142 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (172 : Vertex) [(141 : Vertex), (142 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 38 = false ∨ valuation q 43 = false := by
  rw [value8, value38, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 38 = false ∨ valuation q 65 = false := by
  rw [value8, value38, value44, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 43 = false ∨ valuation q 55 = false := by
  rw [value8, value43, value44, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (140 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E257.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112257
