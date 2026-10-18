import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 68 = false := by
  rw [value52, value55, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 77 = false := by
  rw [value52, value55, value58, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 95 = false := by
  rw [value52, value55, value58, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 57 = false ∨ valuation q 68 = false := by
  rw [value52, value57, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (270 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 57 = false ∨ valuation q 77 = false := by
  rw [value52, value57, value58, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (270 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 57 = false ∨ valuation q 95 = false := by
  rw [value52, value57, value58, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (270 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 77 = false := by
  rw [value52, value58, value68, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 95 = false := by
  rw [value52, value58, value68, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (287 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 52 = false ∨ valuation q 77 = false ∨ valuation q 95 = false := by
  rw [value52, value58, value77, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 68 = false := by
  rw [value55, value57, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (270 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 77 = false := by
  rw [value55, value57, value58, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (270 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 95 = false := by
  rw [value55, value57, value58, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (270 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 68 = false ∨ valuation q 77 = false := by
  rw [value55, value58, value68, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 68 = false ∨ valuation q 95 = false := by
  rw [value55, value58, value68, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (287 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 77 = false ∨ valuation q 95 = false := by
  rw [value55, value58, value77, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 68 = false ∨ valuation q 77 = false := by
  rw [value57, value58, value68, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (270 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 68 = false ∨ valuation q 95 = false := by
  rw [value57, value58, value68, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (270 : Vertex) (287 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 77 = false ∨ valuation q 95 = false := by
  rw [value57, value58, value77, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (270 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 68 = false ∨ valuation q 77 = false ∨ valuation q 95 = false := by
  rw [value58, value68, value77, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (287 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value9, value47, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (257 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 47 = false ∨ valuation q 62 = false := by
  rw [value9, value47, value59, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (257 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 47 = false ∨ valuation q 65 = false := by
  rw [value9, value47, value59, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (257 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 47 = false ∨ valuation q 78 = false := by
  rw [value9, value47, value59, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (257 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 47 = false ∨ valuation q 96 = false := by
  rw [value9, value47, value59, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (257 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value9, value59, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (275 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value9, value59, value60, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (275 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 60 = false ∨ valuation q 78 = false := by
  rw [value9, value59, value60, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (275 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 60 = false ∨ valuation q 96 = false := by
  rw [value9, value59, value60, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (275 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value9, value59, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (277 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 62 = false ∨ valuation q 78 = false := by
  rw [value9, value59, value62, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (277 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 62 = false ∨ valuation q 96 = false := by
  rw [value9, value59, value62, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (277 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 9 = false ∨ valuation q 65 = false ∨ valuation q 78 = false := by
  rw [value9, value59, value65, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (281 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E081.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112081
