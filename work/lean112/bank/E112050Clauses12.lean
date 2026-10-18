import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 86 = false ∨ valuation q 99 = false := by
  rw [value17, value86, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value17, value88, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (390 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value17, value88, value99, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (404 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value86, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (389 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value86, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (389 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value86, value88, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (390 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 53 = false ∨ valuation q 88 = false := by
  rw [value18, value53, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 53 = false ∨ valuation q 91 = false := by
  rw [value18, value53, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 53 = false ∨ valuation q 96 = false := by
  rw [value18, value53, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 53 = false ∨ valuation q 100 = false := by
  rw [value18, value53, value89, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 53 = false ∨ valuation q 113 = false := by
  rw [value18, value53, value89, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value18, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value18, value88, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value18, value88, value89, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 88 = false ∨ valuation q 113 = false := by
  rw [value18, value88, value89, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value18, value89, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value18, value89, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (391 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value18, value89, value91, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value18, value89, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (397 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 96 = false ∨ valuation q 113 = false := by
  rw [value18, value89, value96, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value18, value89, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value53, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value53, value88, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (388 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value53, value88, value89, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (388 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 113 = false := by
  rw [value53, value88, value89, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (388 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value53, value89, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value53, value89, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (391 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value53, value89, value91, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value53, value89, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (397 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 96 = false ∨ valuation q 113 = false := by
  rw [value53, value89, value96, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (397 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 53 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value53, value89, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value88, value89, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (388 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E050.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112050
