import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 37 = false ∨ valuation q 106 = false := by
  rw [value18, value36, value37, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (94 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value32, value34, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (84 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 106 = false := by
  rw [value32, value34, value36, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (84 : Vertex) (88 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 106 = false := by
  rw [value32, value36, value37, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (84 : Vertex) (94 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 106 = false := by
  rw [value34, value36, value37, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (88 : Vertex) (94 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 18 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 106 = true := by
  rw [value18, value34, value36, value37, value106, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(28 : Vertex), (88 : Vertex), (94 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (84 : Vertex) [(28 : Vertex), (88 : Vertex), (94 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 18 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 106 = true := by
  rw [value18, value32, value34, value36, value106, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(28 : Vertex), (84 : Vertex), (88 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (94 : Vertex) [(28 : Vertex), (84 : Vertex), (88 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 65 = false := by
  rw [value35, value36, value37, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (90 : Vertex) (92 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 165 = true ∨ valuation q 36 = true ∨ valuation q 65 = true ∨ valuation q 107 = true := by
  rw [value36, value37, value65, value107, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(92 : Vertex), (222 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (90 : Vertex) [(92 : Vertex), (222 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 165 = true ∨ valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 107 = true := by
  rw [value35, value36, value37, value107, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(90 : Vertex), (92 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (222 : Vertex) [(90 : Vertex), (92 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 165 = true ∨ valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 65 = true := by
  rw [value35, value36, value37, value65, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(90 : Vertex), (92 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (350 : Vertex) [(90 : Vertex), (92 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 38 = true := by
  rw [value38, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (131 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 42 = true ∨ valuation q 46 = true := by
  rw [value38, value42, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ∈ [(135 : Vertex), (139 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (131 : Vertex) [(135 : Vertex), (139 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 166 = true ∨ valuation q 46 = true := by
  rw [value38, value46, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 166 = true ∨ valuation q 42 = true := by
  rw [value38, value42, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (139 : Vertex) [(135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value39, value40, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (134 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 39 = false ∨ valuation q 59 = false := by
  rw [value4, value39, value40, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (132 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 42 = false ∨ valuation q 59 = false := by
  rw [value4, value40, value42, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (135 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value4, value40, value47, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (141 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value4, value40, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (149 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 59 = false := by
  rw [value39, value40, value42, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value39, value40, value47, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (141 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 59 = false ∨ valuation q 112 = false := by
  rw [value39, value40, value59, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value40, value42, value47, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (141 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value40, value42, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (149 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 59 = false ∨ valuation q 112 = false := by
  rw [value40, value42, value59, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 47 = false ∨ valuation q 59 = false ∨ valuation q 112 = false := by
  rw [value40, value47, value59, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (141 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 41 = true := by
  rw [value41, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (134 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 51 = true := by
  rw [value39, value41, value42, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ∈ [(132 : Vertex), (135 : Vertex), (150 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (134 : Vertex) [(132 : Vertex), (135 : Vertex), (150 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 169 = true ∨ valuation q 42 = true ∨ valuation q 51 = true := by
  rw [value41, value42, value51, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(135 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (132 : Vertex) [(135 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 169 = true ∨ valuation q 39 = true ∨ valuation q 51 = true := by
  rw [value39, value41, value51, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(132 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (135 : Vertex) [(132 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 169 = true ∨ valuation q 39 = true ∨ valuation q 42 = true := by
  rw [value39, value41, value42, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(132 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (150 : Vertex) [(132 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E055.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112055
