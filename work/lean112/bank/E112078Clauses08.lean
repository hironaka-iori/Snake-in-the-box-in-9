import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 55 = false ∨ valuation q 106 = false := by
  rw [value43, value46, value55, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (205 : Vertex) (217 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 39 = false := by
  rw [value7, value26, value39, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (138 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 47 = false := by
  rw [value7, value26, value44, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (138 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 56 = false := by
  rw [value7, value26, value44, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (138 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 107 = false := by
  rw [value7, value26, value44, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (138 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 39 = false ∨ valuation q 47 = false := by
  rw [value7, value39, value44, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (194 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 39 = false ∨ valuation q 56 = false := by
  rw [value7, value39, value44, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 47 = false ∨ valuation q 56 = false := by
  rw [value7, value44, value47, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (206 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 47 = false ∨ valuation q 107 = false := by
  rw [value7, value44, value47, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (206 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 56 = false ∨ valuation q 107 = false := by
  rw [value7, value44, value56, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (218 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 26 = false ∨ valuation q 39 = false ∨ valuation q 47 = false := by
  rw [value26, value39, value44, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (194 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 26 = false ∨ valuation q 39 = false ∨ valuation q 56 = false := by
  rw [value26, value39, value44, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 26 = false ∨ valuation q 47 = false ∨ valuation q 56 = false := by
  rw [value26, value44, value47, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (206 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 26 = false ∨ valuation q 47 = false ∨ valuation q 107 = false := by
  rw [value26, value44, value47, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (206 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 26 = false ∨ valuation q 56 = false ∨ valuation q 107 = false := by
  rw [value26, value44, value56, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (138 : Vertex) (218 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 56 = false ∨ valuation q 107 = false := by
  rw [value44, value47, value56, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (206 : Vertex) (218 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 46 = false := by
  rw [value8, value27, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 47 = false := by
  rw [value8, value27, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 57 = false := by
  rw [value8, value27, value45, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 109 = false := by
  rw [value8, value27, value45, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value8, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 57 = false := by
  rw [value8, value45, value46, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 109 = false := by
  rw [value8, value45, value46, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (205 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 47 = false ∨ valuation q 57 = false := by
  rw [value8, value45, value47, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 47 = false ∨ valuation q 109 = false := by
  rw [value8, value45, value47, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 8 = false ∨ valuation q 57 = false ∨ valuation q 109 = false := by
  rw [value8, value45, value57, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 27 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value27, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 27 = false ∨ valuation q 46 = false ∨ valuation q 57 = false := by
  rw [value27, value45, value46, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 27 = false ∨ valuation q 46 = false ∨ valuation q 109 = false := by
  rw [value27, value45, value46, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (205 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 27 = false ∨ valuation q 47 = false ∨ valuation q 57 = false := by
  rw [value27, value45, value47, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 27 = false ∨ valuation q 47 = false ∨ valuation q 109 = false := by
  rw [value27, value45, value47, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 27 = false ∨ valuation q 57 = false ∨ valuation q 109 = false := by
  rw [value27, value45, value57, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E078.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112078
