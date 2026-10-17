import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 70 = false := by
  rw [value57, value59, value60, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (204 : Vertex) (207 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 177 = true ∨ valuation q 18 = true ∨ valuation q 38 = true ∨ valuation q 56 = true ∨ valuation q 57 = true ∨ valuation q 60 = true ∨ valuation q 108 = true := by
  rw [value18, value38, value56, value57, value59, value60, value108, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(78 : Vertex), (142 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (222 : Vertex) [(78 : Vertex), (142 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 39 = false ∨ valuation q 54 = false := by
  rw [value19, value39, value54, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 39 = false ∨ valuation q 58 = false := by
  rw [value19, value39, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (143 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 39 = false ∨ valuation q 59 = false := by
  rw [value19, value39, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (143 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 39 = false ∨ valuation q 71 = false := by
  rw [value19, value39, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (143 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 39 = false ∨ valuation q 109 = false := by
  rw [value19, value39, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (143 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 54 = false ∨ valuation q 58 = false := by
  rw [value19, value54, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 54 = false ∨ valuation q 59 = false := by
  rw [value19, value54, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (199 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 54 = false ∨ valuation q 71 = false := by
  rw [value19, value54, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (199 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 54 = false ∨ valuation q 109 = false := by
  rw [value19, value54, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (199 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value19, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 58 = false ∨ valuation q 71 = false := by
  rw [value19, value58, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (205 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 58 = false ∨ valuation q 109 = false := by
  rw [value19, value58, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (205 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 59 = false ∨ valuation q 71 = false := by
  rw [value19, value59, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (206 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 59 = false ∨ valuation q 109 = false := by
  rw [value19, value59, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 19 = false ∨ valuation q 71 = false ∨ valuation q 109 = false := by
  rw [value19, value60, value71, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (223 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 54 = false ∨ valuation q 58 = false := by
  rw [value39, value54, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 54 = false ∨ valuation q 59 = false := by
  rw [value39, value54, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (199 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 54 = false ∨ valuation q 71 = false := by
  rw [value39, value54, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (199 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 54 = false ∨ valuation q 109 = false := by
  rw [value39, value54, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (199 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value39, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 58 = false ∨ valuation q 71 = false := by
  rw [value39, value58, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (205 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 58 = false ∨ valuation q 109 = false := by
  rw [value39, value58, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (205 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 59 = false ∨ valuation q 71 = false := by
  rw [value39, value59, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (206 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 59 = false ∨ valuation q 109 = false := by
  rw [value39, value59, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 71 = false ∨ valuation q 109 = false := by
  rw [value39, value60, value71, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (143 : Vertex) (223 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value54, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 58 = false ∨ valuation q 71 = false := by
  rw [value54, value58, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 58 = false ∨ valuation q 109 = false := by
  rw [value54, value58, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 59 = false ∨ valuation q 71 = false := by
  rw [value54, value59, value60, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (206 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 59 = false ∨ valuation q 109 = false := by
  rw [value54, value59, value60, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E158.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112158
