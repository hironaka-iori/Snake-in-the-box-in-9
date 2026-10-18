import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 98 = false := by
  rw [value85, value86, value87, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 107 = false := by
  rw [value85, value86, value87, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value85, value87, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value85, value87, value93, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value85, value87, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (439 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value86, value87, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (422 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value86, value87, value93, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (422 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value86, value87, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (422 : Vertex) (439 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value87, value93, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (431 : Vertex) (439 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 89 = false := by
  rw [value18, value54, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 91 = false := by
  rw [value18, value54, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 99 = false := by
  rw [value18, value54, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 108 = false := by
  rw [value18, value54, value88, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value18, value81, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (416 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 81 = false ∨ valuation q 91 = false := by
  rw [value18, value81, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (416 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 81 = false ∨ valuation q 99 = false := by
  rw [value18, value81, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (416 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 81 = false ∨ valuation q 108 = false := by
  rw [value18, value81, value88, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (416 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value18, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (426 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value18, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value18, value88, value89, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value18, value88, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 91 = false ∨ valuation q 108 = false := by
  rw [value18, value88, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 99 = false ∨ valuation q 108 = false := by
  rw [value18, value88, value99, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 54 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value54, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (426 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 54 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value54, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 54 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value54, value88, value89, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 54 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value54, value88, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 54 = false ∨ valuation q 91 = false ∨ valuation q 108 = false := by
  rw [value54, value88, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 54 = false ∨ valuation q 99 = false ∨ valuation q 108 = false := by
  rw [value54, value88, value99, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value81, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (426 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value81, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value81, value88, value89, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E024.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112024
