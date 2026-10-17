import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 197 = true ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 79 = true ∨ valuation q 105 = true := by
  rw [value67, value73, value75, value79, value105, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(388 : Vertex), (400 : Vertex), (412 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (276 : Vertex) [(388 : Vertex), (400 : Vertex), (412 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 18 = false ∨ valuation q 69 = false ∨ valuation q 81 = false := by
  rw [value18, value69, value76, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 18 = false ∨ valuation q 81 = false := by
  rw [value18, value81, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (407 : Vertex) (279 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 198 = true ∨ valuation q 69 = true ∨ valuation q 81 = true := by
  rw [value69, value76, value81, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(391 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (279 : Vertex) [(391 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 198 = true ∨ valuation q 18 = true ∨ valuation q 81 = true := by
  rw [value18, value76, value81, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(279 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (391 : Vertex) [(279 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 199 = true ∨ valuation q 74 = true := by
  rw [value74, value77, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(401 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (281 : Vertex) [(401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 199 = true ∨ valuation q 19 = true := by
  rw [value19, value77, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(281 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 20 = false ∨ valuation q 70 = false ∨ valuation q 80 = false := by
  rw [value20, value70, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (282 : Vertex) (394 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 200 = true ∨ valuation q 70 = true ∨ valuation q 80 = true := by
  rw [value70, value78, value80, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(394 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (282 : Vertex) [(394 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 200 = true ∨ valuation q 20 = true ∨ valuation q 80 = true := by
  rw [value20, value78, value80, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(282 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (394 : Vertex) [(282 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 200 = true ∨ valuation q 20 = true ∨ valuation q 70 = true := by
  rw [value20, value70, value78, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(282 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (414 : Vertex) [(282 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 75 = false ∨ valuation q 80 = false := by
  rw [value71, value75, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (396 : Vertex) (404 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 80 = false ∨ valuation q 100 = false := by
  rw [value71, value79, value80, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (396 : Vertex) (414 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 100 = false := by
  rw [value75, value79, value80, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (404 : Vertex) (414 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 201 = true ∨ valuation q 75 = true ∨ valuation q 80 = true ∨ valuation q 100 = true := by
  rw [value75, value79, value80, value100, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(404 : Vertex), (414 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (396 : Vertex) [(404 : Vertex), (414 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 201 = true ∨ valuation q 71 = true ∨ valuation q 80 = true ∨ valuation q 100 = true := by
  rw [value71, value79, value80, value100, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(396 : Vertex), (414 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (404 : Vertex) [(396 : Vertex), (414 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 201 = true ∨ valuation q 71 = true ∨ valuation q 75 = true ∨ valuation q 100 = true := by
  rw [value71, value75, value79, value100, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(396 : Vertex), (404 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(396 : Vertex), (404 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 201 = true ∨ valuation q 71 = true ∨ valuation q 75 = true ∨ valuation q 80 = true := by
  rw [value71, value75, value79, value80, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(396 : Vertex), (404 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (444 : Vertex) [(396 : Vertex), (404 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 80 = true := by
  rw [value80, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (414 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value22, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value22, value78, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (410 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value22, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (412 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 79 = false ∨ valuation q 108 = false := by
  rw [value22, value79, value80, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (412 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 22 = false ∨ valuation q 81 = false ∨ valuation q 108 = false := by
  rw [value22, value80, value81, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (286 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value78, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (410 : Vertex) (412 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 108 = false := by
  rw [value78, value79, value80, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (410 : Vertex) (412 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 108 = false := by
  rw [value78, value80, value81, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (410 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 108 = false := by
  rw [value79, value80, value81, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (412 : Vertex) (415 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 202 = true ∨ valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 108 = true := by
  rw [value78, value79, value80, value81, value108, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(410 : Vertex), (412 : Vertex), (415 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (286 : Vertex) [(410 : Vertex), (412 : Vertex), (415 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 202 = true ∨ valuation q 22 = true ∨ valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 108 = true := by
  rw [value22, value78, value79, value80, value108, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(286 : Vertex), (410 : Vertex), (412 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (415 : Vertex) [(286 : Vertex), (410 : Vertex), (412 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 72 = false ∨ valuation q 80 = false := by
  rw [value23, value72, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (399 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 23 = false ∨ valuation q 72 = false ∨ valuation q 101 = false := by
  rw [value23, value72, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (399 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E258.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112258
