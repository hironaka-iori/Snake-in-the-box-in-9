import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value16, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (346 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value16, value82, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (346 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 116 = false := by
  rw [value16, value82, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value16, value83, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 83 = false ∨ valuation q 116 = false := by
  rw [value16, value83, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (348 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 86 = false ∨ valuation q 116 = false := by
  rw [value16, value85, value86, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (351 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value62, value78, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value62, value78, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (342 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value62, value78, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 78 = false ∨ valuation q 116 = false := by
  rw [value62, value78, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (342 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value62, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (346 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value62, value82, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (346 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 82 = false ∨ valuation q 116 = false := by
  rw [value62, value82, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value62, value83, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 83 = false ∨ valuation q 116 = false := by
  rw [value62, value83, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (348 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 62 = false ∨ valuation q 86 = false ∨ valuation q 116 = false := by
  rw [value62, value85, value86, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (286 : Vertex) (351 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value78, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (346 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value78, value82, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (346 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 116 = false := by
  rw [value78, value82, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value78, value83, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 116 = false := by
  rw [value78, value83, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (348 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 78 = false ∨ valuation q 86 = false ∨ valuation q 116 = false := by
  rw [value78, value85, value86, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (351 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value82, value83, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (346 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 116 = false := by
  rw [value82, value83, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (346 : Vertex) (348 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 116 = false := by
  rw [value82, value85, value86, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (346 : Vertex) (351 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 116 = false := by
  rw [value83, value85, value86, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (348 : Vertex) (351 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 16 = true ∨ valuation q 62 = true ∨ valuation q 78 = true ∨ valuation q 82 = true ∨ valuation q 86 = true ∨ valuation q 116 = true := by
  rw [value16, value62, value78, value82, value85, value86, value116, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(94 : Vertex), (286 : Vertex), (342 : Vertex), (346 : Vertex), (351 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(94 : Vertex), (286 : Vertex), (342 : Vertex), (346 : Vertex), (351 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 63 = false ∨ valuation q 73 = false ∨ valuation q 85 = false := by
  rw [value63, value73, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (335 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 63 = false ∨ valuation q 85 = false ∨ valuation q 117 = false := by
  rw [value63, value85, value86, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (287 : Vertex) (350 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 73 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value73, value79, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (335 : Vertex) (343 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 73 = false ∨ valuation q 79 = false ∨ valuation q 117 = false := by
  rw [value73, value79, value86, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (335 : Vertex) (343 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 73 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value73, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (335 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E064.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112064
