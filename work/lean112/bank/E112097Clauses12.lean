import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 91 = false := by
  rw [value21, value57, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 94 = false := by
  rw [value21, value57, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 114 = false := by
  rw [value21, value57, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 82 = false ∨ valuation q 91 = false := by
  rw [value21, value82, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 82 = false ∨ valuation q 94 = false := by
  rw [value21, value82, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 82 = false ∨ valuation q 114 = false := by
  rw [value21, value82, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (417 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value21, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (432 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 91 = false ∨ valuation q 114 = false := by
  rw [value21, value91, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (432 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value21, value92, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 57 = false ∨ valuation q 82 = false ∨ valuation q 91 = false := by
  rw [value57, value82, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (417 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 57 = false ∨ valuation q 82 = false ∨ valuation q 94 = false := by
  rw [value57, value82, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (417 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 57 = false ∨ valuation q 82 = false ∨ valuation q 114 = false := by
  rw [value57, value82, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (417 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 57 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value57, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (432 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 57 = false ∨ valuation q 91 = false ∨ valuation q 114 = false := by
  rw [value57, value91, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (432 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 57 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value57, value92, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 82 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value82, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (432 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 82 = false ∨ valuation q 91 = false ∨ valuation q 114 = false := by
  rw [value82, value91, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (432 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 82 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value82, value92, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value91, value92, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (432 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value91, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (432 : Vertex) (435 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 216 = true ∨ valuation q 94 = true ∨ valuation q 95 = true := by
  rw [value93, value94, value95, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(435 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (432 : Vertex) [(435 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 58 = false ∨ valuation q 83 = false ∨ valuation q 93 = false := by
  rw [value58, value83, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 217 = true ∨ valuation q 58 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value58, value92, value93, value94, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(307 : Vertex), (433 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (419 : Vertex) [(307 : Vertex), (433 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 217 = true ∨ valuation q 58 = true ∨ valuation q 83 = true ∨ valuation q 93 = true := by
  rw [value58, value83, value93, value94, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(307 : Vertex), (419 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (433 : Vertex) [(307 : Vertex), (419 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 217 = true ∨ valuation q 58 = true ∨ valuation q 83 = true ∨ valuation q 92 = true := by
  rw [value58, value83, value92, value94, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(307 : Vertex), (419 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (434 : Vertex) [(307 : Vertex), (419 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 24 = false ∨ valuation q 85 = false ∨ valuation q 93 = false := by
  rw [value24, value85, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (438 : Vertex) (182 : Vertex) (422 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 24 = false ∨ valuation q 93 = false ∨ valuation q 99 = false := by
  rw [value24, value93, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (438 : Vertex) (182 : Vertex) (434 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 24 = false ∨ valuation q 93 = false ∨ valuation q 117 = false := by
  rw [value24, value93, value95, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (438 : Vertex) (182 : Vertex) (434 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 93 = false ∨ valuation q 99 = false ∨ valuation q 117 = false := by
  rw [value93, value95, value99, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (438 : Vertex) (434 : Vertex) (446 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 218 = true ∨ valuation q 85 = true ∨ valuation q 93 = true ∨ valuation q 99 = true ∨ valuation q 117 = true := by
  rw [value85, value93, value95, value99, value117, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(422 : Vertex), (434 : Vertex), (446 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (182 : Vertex) [(422 : Vertex), (434 : Vertex), (446 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 218 = true ∨ valuation q 24 = true ∨ valuation q 93 = true ∨ valuation q 99 = true ∨ valuation q 117 = true := by
  rw [value24, value93, value95, value99, value117, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(182 : Vertex), (434 : Vertex), (446 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (422 : Vertex) [(182 : Vertex), (434 : Vertex), (446 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 218 = true ∨ valuation q 24 = true ∨ valuation q 85 = true ∨ valuation q 99 = true ∨ valuation q 117 = true := by
  rw [value24, value85, value95, value99, value117, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(182 : Vertex), (422 : Vertex), (446 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (434 : Vertex) [(182 : Vertex), (422 : Vertex), (446 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E097.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112097
