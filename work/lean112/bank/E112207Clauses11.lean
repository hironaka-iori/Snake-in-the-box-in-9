import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 172 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value48, value52, value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (264 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex), (264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value50, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 57 = false := by
  rw [value50, value53, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value50, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (268 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value53, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (266 : Vertex) (268 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value53, value55, value56, value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(266 : Vertex), (268 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (262 : Vertex) [(266 : Vertex), (268 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value50, value55, value56, value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(262 : Vertex), (268 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (266 : Vertex) [(262 : Vertex), (268 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 57 = true := by
  rw [value50, value53, value56, value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(262 : Vertex), (266 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (268 : Vertex) [(262 : Vertex), (266 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value7, value51, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value7, value51, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 51 = false ∨ valuation q 76 = false := by
  rw [value7, value51, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value7, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 67 = false := by
  rw [value7, value54, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 76 = false := by
  rw [value7, value54, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 56 = false ∨ valuation q 67 = false := by
  rw [value7, value56, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (270 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 67 = false ∨ valuation q 76 = false := by
  rw [value7, value57, value67, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value8, value58, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (275 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value8, value58, value59, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (275 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 59 = false ∨ valuation q 77 = false := by
  rw [value8, value58, value59, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (275 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 59 = false ∨ valuation q 96 = false := by
  rw [value8, value58, value59, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (275 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value8, value58, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (277 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 61 = false ∨ valuation q 77 = false := by
  rw [value8, value58, value61, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (277 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 61 = false ∨ valuation q 96 = false := by
  rw [value8, value58, value61, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (277 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 64 = false ∨ valuation q 77 = false := by
  rw [value8, value58, value64, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (281 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 64 = false ∨ valuation q 96 = false := by
  rw [value8, value58, value64, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (281 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 8 = false ∨ valuation q 77 = false ∨ valuation q 96 = false := by
  rw [value8, value58, value77, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (337 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 46 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value46, value58, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (275 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 46 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value46, value58, value59, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (275 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 46 = false ∨ valuation q 59 = false ∨ valuation q 96 = false := by
  rw [value46, value58, value59, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (275 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 46 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value46, value58, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (257 : Vertex) (277 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 77 = false := by
  rw [value58, value59, value64, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (275 : Vertex) (281 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 96 = false := by
  rw [value58, value59, value64, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (275 : Vertex) (281 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E207.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112207
