import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 76 = false ∨ valuation q 80 = false := by
  rw [value23, value76, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 76 = false ∨ valuation q 101 = false := by
  rw [value23, value76, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value23, value80, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (414 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 72 = false ∨ valuation q 76 = false ∨ valuation q 80 = false := by
  rw [value72, value76, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 72 = false ∨ valuation q 76 = false ∨ valuation q 101 = false := by
  rw [value72, value76, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (407 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 72 = false ∨ valuation q 76 = false ∨ valuation q 109 = false := by
  rw [value72, value76, value81, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (407 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value72, value80, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (414 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 109 = false := by
  rw [value72, value80, value81, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (414 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 72 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value72, value81, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (447 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 76 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value76, value80, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (414 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 76 = false ∨ valuation q 80 = false ∨ valuation q 109 = false := by
  rw [value76, value80, value81, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (414 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 76 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value76, value81, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (447 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value80, value81, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (414 : Vertex) (447 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 64 = true ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 110 = true := by
  rw [value64, value82, value83, value87, value110, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(384 : Vertex), (418 : Vertex), (424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (288 : Vertex) [(384 : Vertex), (418 : Vertex), (424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 24 = true ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 110 = true := by
  rw [value24, value82, value83, value87, value110, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(288 : Vertex), (418 : Vertex), (424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (384 : Vertex) [(288 : Vertex), (418 : Vertex), (424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 24 = true ∨ valuation q 64 = true ∨ valuation q 87 = true ∨ valuation q 110 = true := by
  rw [value24, value64, value82, value87, value110, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(288 : Vertex), (384 : Vertex), (424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (418 : Vertex) [(288 : Vertex), (384 : Vertex), (424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 24 = true ∨ valuation q 64 = true ∨ valuation q 83 = true ∨ valuation q 110 = true := by
  rw [value24, value64, value82, value83, value110, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(288 : Vertex), (384 : Vertex), (418 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (424 : Vertex) [(288 : Vertex), (384 : Vertex), (418 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 24 = true ∨ valuation q 64 = true ∨ valuation q 83 = true ∨ valuation q 87 = true := by
  rw [value24, value64, value82, value83, value87, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(288 : Vertex), (384 : Vertex), (418 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (480 : Vertex) [(288 : Vertex), (384 : Vertex), (418 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 66 = false ∨ valuation q 82 = false := by
  rw [value25, value66, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (386 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 66 = false ∨ valuation q 84 = false := by
  rw [value25, value66, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (386 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 66 = false ∨ valuation q 86 = false := by
  rw [value25, value66, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (386 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 66 = false ∨ valuation q 94 = false := by
  rw [value25, value66, value83, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (386 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 66 = false ∨ valuation q 111 = false := by
  rw [value25, value66, value83, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (386 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value25, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (416 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value25, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (416 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 82 = false ∨ valuation q 94 = false := by
  rw [value25, value82, value83, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (416 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value25, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (419 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 84 = false ∨ valuation q 94 = false := by
  rw [value25, value83, value84, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (419 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 86 = false ∨ valuation q 94 = false := by
  rw [value25, value83, value86, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (422 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 111 = false := by
  rw [value25, value83, value94, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (290 : Vertex) (434 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 66 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value66, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (386 : Vertex) (416 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 66 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value66, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (386 : Vertex) (416 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E258.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112258
