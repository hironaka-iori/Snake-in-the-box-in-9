import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value17, value82, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value17, value83, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value17, value83, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 95 = false ∨ valuation q 102 = false := by
  rw [value17, value83, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value52, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (385 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value52, value81, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (385 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 81 = false ∨ valuation q 95 = false := by
  rw [value52, value81, value83, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (385 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value52, value81, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (385 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value52, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 82 = false ∨ valuation q 95 = false := by
  rw [value52, value82, value83, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value52, value82, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value52, value83, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value52, value83, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 52 = false ∨ valuation q 95 = false ∨ valuation q 102 = false := by
  rw [value52, value83, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value81, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 95 = false := by
  rw [value81, value82, value83, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value81, value82, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value81, value83, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value81, value83, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 95 = false ∨ valuation q 102 = false := by
  rw [value81, value83, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (385 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value82, value83, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value82, value83, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 95 = false ∨ valuation q 102 = false := by
  rw [value82, value83, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 95 = false ∨ valuation q 102 = false := by
  rw [value83, value85, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (391 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 201 = true ∨ valuation q 17 = true ∨ valuation q 52 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 95 = true ∨ valuation q 102 = true := by
  rw [value17, value52, value82, value83, value85, value95, value102, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (387 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(131 : Vertex), (259 : Vertex), (386 : Vertex), (391 : Vertex), (403 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (387 : Vertex) (385 : Vertex) [(131 : Vertex), (259 : Vertex), (386 : Vertex), (391 : Vertex), (403 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 201 = true ∨ valuation q 17 = true ∨ valuation q 52 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 95 = true ∨ valuation q 102 = true := by
  rw [value17, value52, value81, value83, value85, value95, value102, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (387 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(131 : Vertex), (259 : Vertex), (385 : Vertex), (391 : Vertex), (403 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (387 : Vertex) (386 : Vertex) [(131 : Vertex), (259 : Vertex), (385 : Vertex), (391 : Vertex), (403 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 201 = true ∨ valuation q 17 = true ∨ valuation q 52 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 102 = true := by
  rw [value17, value52, value81, value82, value83, value85, value102, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (387 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(131 : Vertex), (259 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (387 : Vertex) (403 : Vertex) [(131 : Vertex), (259 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 201 = true ∨ valuation q 17 = true ∨ valuation q 52 = true ∨ valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 95 = true := by
  rw [value17, value52, value81, value82, value83, value85, value95, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (387 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(131 : Vertex), (259 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (387 : Vertex) (451 : Vertex) [(131 : Vertex), (259 : Vertex), (385 : Vertex), (386 : Vertex), (391 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 54 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value54, value81, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 54 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value54, value81, value84, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 54 = false ∨ valuation q 81 = false ∨ valuation q 104 = false := by
  rw [value54, value81, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 54 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value54, value84, value85, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E027.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112027
