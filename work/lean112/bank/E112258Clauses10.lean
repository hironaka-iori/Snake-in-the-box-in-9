import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 71 = false ∨ valuation q 75 = false ∨ valuation q 103 = false := by
  rw [value67, value71, value75, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (396 : Vertex) (404 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 71 = true ∨ valuation q 75 = true ∨ valuation q 103 = true := by
  rw [value64, value67, value71, value75, value103, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(384 : Vertex), (396 : Vertex), (404 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (389 : Vertex) [(384 : Vertex), (396 : Vertex), (404 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 75 = true ∨ valuation q 103 = true := by
  rw [value64, value67, value68, value75, value103, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(384 : Vertex), (389 : Vertex), (404 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (396 : Vertex) [(384 : Vertex), (389 : Vertex), (404 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 71 = true ∨ valuation q 103 = true := by
  rw [value64, value67, value68, value71, value103, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(384 : Vertex), (389 : Vertex), (396 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (404 : Vertex) [(384 : Vertex), (389 : Vertex), (396 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 71 = true ∨ valuation q 75 = true := by
  rw [value64, value67, value68, value71, value75, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(384 : Vertex), (389 : Vertex), (396 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (452 : Vertex) [(384 : Vertex), (389 : Vertex), (396 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 8 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value8, value65, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 8 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value8, value65, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 8 = false ∨ valuation q 65 = false ∨ valuation q 85 = false := by
  rw [value8, value65, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 8 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value8, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 8 = false ∨ valuation q 67 = false ∨ valuation q 85 = false := by
  rw [value8, value67, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (388 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 8 = false ∨ valuation q 69 = false ∨ valuation q 85 = false := by
  rw [value8, value68, value69, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (391 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value65, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 85 = false := by
  rw [value65, value67, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (388 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 85 = false := by
  rw [value65, value68, value69, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (391 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 69 = false ∨ valuation q 85 = false := by
  rw [value67, value68, value69, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (388 : Vertex) (391 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value65, value67, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (389 : Vertex) (385 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 190 = true ∨ valuation q 8 = true ∨ valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 69 = true := by
  rw [value8, value65, value67, value68, value69, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(261 : Vertex), (385 : Vertex), (388 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (421 : Vertex) [(261 : Vertex), (385 : Vertex), (388 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 76 = false := by
  rw [value68, value69, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (389 : Vertex) (399 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 191 = true ∨ valuation q 68 = true ∨ valuation q 72 = true ∨ valuation q 76 = true := by
  rw [value68, value69, value72, value76, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(389 : Vertex), (399 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (263 : Vertex) [(389 : Vertex), (399 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 191 = true ∨ valuation q 9 = true ∨ valuation q 72 = true ∨ valuation q 76 = true := by
  rw [value9, value69, value72, value76, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(263 : Vertex), (399 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (389 : Vertex) [(263 : Vertex), (399 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 191 = true ∨ valuation q 9 = true ∨ valuation q 68 = true ∨ valuation q 76 = true := by
  rw [value9, value68, value69, value76, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(263 : Vertex), (389 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (399 : Vertex) [(263 : Vertex), (389 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 191 = true ∨ valuation q 9 = true ∨ valuation q 68 = true ∨ valuation q 72 = true := by
  rw [value9, value68, value69, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(263 : Vertex), (389 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (407 : Vertex) [(263 : Vertex), (389 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 66 = false ∨ valuation q 78 = false := by
  rw [value66, value78, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (394 : Vertex) (386 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 192 = true ∨ valuation q 78 = true := by
  rw [value70, value78, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(410 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (386 : Vertex) [(410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 192 = true ∨ valuation q 66 = true := by
  rw [value66, value70, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(386 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (410 : Vertex) [(386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 12 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value12, value67, value71, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (388 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 12 = false ∨ valuation q 67 = false ∨ valuation q 90 = false := by
  rw [value12, value67, value71, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (388 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 12 = false ∨ valuation q 79 = false ∨ valuation q 90 = false := by
  rw [value12, value71, value79, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (412 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 67 = false ∨ valuation q 79 = false ∨ valuation q 90 = false := by
  rw [value67, value71, value79, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (412 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 12 = false ∨ valuation q 79 = false := by
  rw [value12, value79, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (396 : Vertex) (268 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value67, value79, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (396 : Vertex) (388 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 193 = true ∨ valuation q 67 = true ∨ valuation q 79 = true ∨ valuation q 90 = true := by
  rw [value67, value71, value79, value90, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(388 : Vertex), (412 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (268 : Vertex) [(388 : Vertex), (412 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E258.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112258
