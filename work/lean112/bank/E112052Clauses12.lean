import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 71 = false ∨ valuation q 122 = false := by
  rw [value62, value71, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (327 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value62, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 77 = false ∨ valuation q 84 = false := by
  rw [value62, value77, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (341 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 77 = false ∨ valuation q 122 = false := by
  rw [value62, value77, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (341 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value62, value78, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 78 = false ∨ valuation q 122 = false := by
  rw [value62, value78, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (342 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 84 = false ∨ valuation q 122 = false := by
  rw [value62, value79, value84, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (351 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value71, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 84 = false := by
  rw [value71, value77, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (341 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 122 = false := by
  rw [value71, value77, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (341 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value71, value78, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 122 = false := by
  rw [value71, value78, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (342 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 84 = false ∨ valuation q 122 = false := by
  rw [value71, value79, value84, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (327 : Vertex) (351 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value77, value78, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (341 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 122 = false := by
  rw [value77, value78, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (341 : Vertex) (342 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 77 = false ∨ valuation q 84 = false ∨ valuation q 122 = false := by
  rw [value77, value79, value84, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (341 : Vertex) (351 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 78 = false ∨ valuation q 84 = false ∨ valuation q 122 = false := by
  rw [value78, value79, value84, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (342 : Vertex) (351 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value8, value63, value72, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 63 = false ∨ valuation q 81 = false := by
  rw [value8, value63, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (280 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 63 = false ∨ valuation q 82 = false := by
  rw [value8, value63, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (280 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 63 = false ∨ valuation q 123 = false := by
  rw [value8, value63, value80, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (280 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value8, value72, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (328 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 72 = false ∨ valuation q 82 = false := by
  rw [value8, value72, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (328 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 72 = false ∨ valuation q 123 = false := by
  rw [value8, value72, value80, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (328 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value8, value80, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 81 = false ∨ valuation q 123 = false := by
  rw [value8, value80, value81, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (345 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 8 = false ∨ valuation q 82 = false ∨ valuation q 123 = false := by
  rw [value8, value80, value82, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (88 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 63 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value63, value72, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (280 : Vertex) (328 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 63 = false ∨ valuation q 72 = false ∨ valuation q 82 = false := by
  rw [value63, value72, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (280 : Vertex) (328 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 63 = false ∨ valuation q 72 = false ∨ valuation q 123 = false := by
  rw [value63, value72, value80, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (280 : Vertex) (328 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 63 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value63, value80, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (280 : Vertex) (345 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 63 = false ∨ valuation q 81 = false ∨ valuation q 123 = false := by
  rw [value63, value80, value81, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (344 : Vertex) (280 : Vertex) (345 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E052.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112052
