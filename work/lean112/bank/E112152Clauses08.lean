import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 100 = false ∨ valuation q 112 = false := by
  rw [value44, value100, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 79 = false ∨ valuation q 99 = false := by
  rw [value62, value79, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 79 = false ∨ valuation q 100 = false := by
  rw [value62, value79, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 79 = false ∨ valuation q 112 = false := by
  rw [value62, value79, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (419 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value62, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (481 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value62, value99, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 100 = false ∨ valuation q 112 = false := by
  rw [value62, value100, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (355 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 79 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value79, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (419 : Vertex) (481 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 79 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value79, value99, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (419 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 79 = false ∨ valuation q 100 = false ∨ valuation q 112 = false := by
  rw [value79, value100, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (419 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 112 = false := by
  rw [value99, value100, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 46 = false ∨ valuation q 63 = false ∨ valuation q 80 = false := by
  rw [value46, value63, value80, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (357 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 46 = false ∨ valuation q 63 = false ∨ valuation q 113 = false := by
  rw [value46, value63, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (357 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 46 = false ∨ valuation q 80 = false ∨ valuation q 99 = false := by
  rw [value46, value80, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 80 = false ∨ valuation q 113 = false := by
  rw [value63, value80, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (357 : Vertex) (421 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value63, value99, value102, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (357 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value63, value99, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (357 : Vertex) (481 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value63, value102, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (357 : Vertex) (493 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value80, value99, value102, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (421 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 113 = false := by
  rw [value80, value99, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (421 : Vertex) (481 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 99 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value99, value102, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (481 : Vertex) (493 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 64 = false ∨ valuation q 100 = false := by
  rw [value47, value64, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (358 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 64 = false ∨ valuation q 114 = false := by
  rw [value47, value64, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (358 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value47, value81, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 81 = false ∨ valuation q 108 = false := by
  rw [value47, value81, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 81 = false ∨ valuation q 114 = false := by
  rw [value47, value81, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value47, value100, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 108 = false ∨ valuation q 114 = false := by
  rw [value47, value103, value108, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (494 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value64, value81, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (358 : Vertex) (422 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 81 = false ∨ valuation q 114 = false := by
  rw [value64, value81, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (358 : Vertex) (422 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value64, value100, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (358 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 64 = false ∨ valuation q 100 = false ∨ valuation q 114 = false := by
  rw [value64, value100, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (358 : Vertex) (482 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E152.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112152
