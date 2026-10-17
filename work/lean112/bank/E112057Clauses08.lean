import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 13 = true ∨ valuation q 32 = true := by
  rw [value13, value32, value33, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(21 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (69 : Vertex) [(21 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 13 = true ∨ valuation q 23 = true := by
  rw [value13, value23, value33, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(21 : Vertex), (69 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (84 : Vertex) [(21 : Vertex), (69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 35 = false := by
  rw [value26, value30, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (80 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 36 = false := by
  rw [value26, value30, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (80 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value26, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (90 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 30 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value30, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (80 : Vertex) (90 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 26 = false ∨ valuation q 30 = false := by
  rw [value26, value30, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (88 : Vertex) (72 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 161 = true ∨ valuation q 30 = true ∨ valuation q 35 = true ∨ valuation q 36 = true := by
  rw [value30, value34, value35, value36, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(80 : Vertex), (90 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (72 : Vertex) [(80 : Vertex), (90 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 161 = true ∨ valuation q 26 = true ∨ valuation q 30 = true ∨ valuation q 36 = true := by
  rw [value26, value30, value34, value36, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(72 : Vertex), (80 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (90 : Vertex) [(72 : Vertex), (80 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value31, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 162 = true ∨ valuation q 34 = true ∨ valuation q 37 = true := by
  rw [value34, value35, value37, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(88 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (82 : Vertex) [(88 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 162 = true ∨ valuation q 31 = true ∨ valuation q 37 = true := by
  rw [value31, value35, value37, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(82 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (88 : Vertex) [(82 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 162 = true ∨ valuation q 31 = true ∨ valuation q 34 = true := by
  rw [value31, value34, value35, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(82 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (94 : Vertex) [(82 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value18, value32, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 37 = false := by
  rw [value18, value32, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (84 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 106 = false := by
  rw [value18, value32, value36, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (84 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value18, value34, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 106 = false := by
  rw [value18, value34, value36, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (88 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 37 = false ∨ valuation q 106 = false := by
  rw [value18, value36, value37, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (94 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value32, value34, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (84 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 163 = true ∨ valuation q 18 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 106 = true := by
  rw [value18, value34, value36, value37, value106, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(28 : Vertex), (88 : Vertex), (94 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (84 : Vertex) [(28 : Vertex), (88 : Vertex), (94 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 163 = true ∨ valuation q 18 = true ∨ valuation q 32 = true ∨ valuation q 37 = true ∨ valuation q 106 = true := by
  rw [value18, value32, value36, value37, value106, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(28 : Vertex), (84 : Vertex), (94 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (88 : Vertex) [(28 : Vertex), (84 : Vertex), (94 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 64 = false := by
  rw [value35, value36, value37, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (90 : Vertex) (92 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 107 = false := by
  rw [value35, value36, value37, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (90 : Vertex) (92 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 42 = true ∨ valuation q 46 = true := by
  rw [value38, value42, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ∈ [(135 : Vertex), (139 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (131 : Vertex) [(135 : Vertex), (139 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 165 = true ∨ valuation q 46 = true := by
  rw [value38, value46, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 165 = true ∨ valuation q 42 = true := by
  rw [value38, value42, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (139 : Vertex) [(135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value39, value40, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (134 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 166 = true ∨ valuation q 41 = true ∨ valuation q 49 = true := by
  rw [value39, value41, value49, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(134 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (133 : Vertex) [(134 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 166 = true ∨ valuation q 40 = true ∨ valuation q 49 = true := by
  rw [value39, value40, value49, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(133 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (134 : Vertex) [(133 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 166 = true ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value39, value40, value41, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(133 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (148 : Vertex) [(133 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value4, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (132 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E057.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112057
