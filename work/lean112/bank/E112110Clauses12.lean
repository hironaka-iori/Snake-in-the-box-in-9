import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 77 = false ∨ valuation q 96 = false := by
  rw [value35, value77, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (385 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 77 = false ∨ valuation q 99 = false := by
  rw [value35, value77, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (385 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 77 = false ∨ valuation q 100 = false := by
  rw [value35, value77, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (385 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 77 = false ∨ valuation q 109 = false := by
  rw [value35, value77, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (385 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 96 = false ∨ valuation q 99 = false := by
  rw [value35, value96, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value35, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value35, value96, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (448 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value35, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value35, value97, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value35, value97, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 60 = false ∨ valuation q 77 = false ∨ valuation q 99 = false := by
  rw [value60, value77, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (385 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 60 = false ∨ valuation q 77 = false ∨ valuation q 100 = false := by
  rw [value60, value77, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (385 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 60 = false ∨ valuation q 77 = false ∨ valuation q 109 = false := by
  rw [value60, value77, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (385 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 60 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value60, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 60 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value60, value97, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 60 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value60, value97, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 99 = false := by
  rw [value77, value96, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value77, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (448 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value77, value96, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (448 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value77, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value77, value97, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 77 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value77, value97, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (385 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value96, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value96, value97, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value96, value97, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value97, value99, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 35 = true ∨ valuation q 60 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 109 = true := by
  rw [value35, value60, value96, value97, value99, value100, value109, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (385 : Vertex) [(193 : Vertex), (321 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 35 = true ∨ valuation q 60 = true ∨ valuation q 77 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 109 = true := by
  rw [value35, value60, value77, value96, value97, value99, value109, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (453 : Vertex) [(193 : Vertex), (321 : Vertex), (385 : Vertex), (448 : Vertex), (451 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 96 = false ∨ valuation q 99 = false := by
  rw [value78, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 96 = false ∨ valuation q 110 = false := by
  rw [value78, value96, value98, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 99 = false ∨ valuation q 110 = false := by
  rw [value78, value98, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 110 = false := by
  rw [value96, value98, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (448 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E110.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112110
