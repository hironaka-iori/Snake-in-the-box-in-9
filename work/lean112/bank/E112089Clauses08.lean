import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value8, value41, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (137 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 41 = false ∨ valuation q 54 = false := by
  rw [value8, value41, value43, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (137 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 41 = false ∨ valuation q 64 = false := by
  rw [value8, value41, value43, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (137 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 41 = false ∨ valuation q 96 = false := by
  rw [value8, value41, value43, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (137 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value8, value42, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (138 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 42 = false ∨ valuation q 54 = false := by
  rw [value8, value42, value43, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (138 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 42 = false ∨ valuation q 64 = false := by
  rw [value8, value42, value43, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (138 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 42 = false ∨ valuation q 96 = false := by
  rw [value8, value42, value43, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (138 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 45 = false ∨ valuation q 54 = false := by
  rw [value8, value43, value45, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (143 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 45 = false ∨ valuation q 64 = false := by
  rw [value8, value43, value45, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 45 = false ∨ valuation q 96 = false := by
  rw [value8, value43, value45, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value8, value43, value54, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (155 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 54 = false ∨ valuation q 96 = false := by
  rw [value8, value43, value54, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (11 : Vertex) (155 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value41, value42, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (138 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 54 = false := by
  rw [value41, value42, value43, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (138 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 64 = false := by
  rw [value41, value42, value43, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (138 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 96 = false := by
  rw [value41, value42, value43, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (138 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 54 = false := by
  rw [value41, value43, value45, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (143 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 64 = false := by
  rw [value41, value43, value45, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 96 = false := by
  rw [value41, value43, value45, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value41, value43, value54, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (155 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 54 = false ∨ valuation q 96 = false := by
  rw [value41, value43, value54, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (155 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 64 = false ∨ valuation q 96 = false := by
  rw [value41, value43, value64, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 54 = false := by
  rw [value42, value43, value45, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (143 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 64 = false := by
  rw [value42, value43, value45, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 96 = false := by
  rw [value42, value43, value45, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value42, value43, value54, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (155 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 54 = false ∨ valuation q 96 = false := by
  rw [value42, value43, value54, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (155 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 64 = false ∨ valuation q 96 = false := by
  rw [value42, value43, value64, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value43, value45, value54, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (143 : Vertex) (155 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 96 = false := by
  rw [value43, value45, value54, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (143 : Vertex) (155 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 64 = false ∨ valuation q 96 = false := by
  rw [value43, value45, value64, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (143 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E089.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112089
