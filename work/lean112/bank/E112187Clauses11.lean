import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 224 = true ∨ valuation q 65 = true ∨ valuation q 84 = true ∨ valuation q 104 = true := by
  rw [value65, value84, value104, value105, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(357 : Vertex), (421 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (485 : Vertex) (493 : Vertex) [(357 : Vertex), (421 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 115 = false := by
  rw [value66, value85, value106, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (358 : Vertex) (422 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 87 = false ∨ valuation q 103 = false ∨ valuation q 116 = false := by
  rw [value87, value103, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 226 = true ∨ valuation q 87 = true ∨ valuation q 103 = true := by
  rw [value87, value103, value107, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (504 : Vertex) [(424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 108 = true := by
  rw [value108, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (491 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 89 = true ∨ valuation q 110 = true := by
  rw [value89, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ∈ [(427 : Vertex), (495 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (491 : Vertex) [(427 : Vertex), (495 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 227 = true ∨ valuation q 110 = true := by
  rw [value108, value110, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (427 : Vertex) [(495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 227 = true ∨ valuation q 89 = true := by
  rw [value89, value108, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(427 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (495 : Vertex) [(427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 228 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value109, value110, value118, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(495 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (485 : Vertex) [(495 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 228 = true ∨ valuation q 105 = true ∨ valuation q 118 = true := by
  rw [value105, value109, value118, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(485 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (495 : Vertex) [(485 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 228 = true ∨ valuation q 105 = true ∨ valuation q 110 = true := by
  rw [value105, value109, value110, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(485 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (509 : Vertex) [(485 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 92 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value92, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 229 = true ∨ valuation q 92 = true ∨ valuation q 109 = true := by
  rw [value92, value109, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(431 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (491 : Vertex) [(431 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 229 = true ∨ valuation q 92 = true ∨ valuation q 108 = true := by
  rw [value92, value108, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(431 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (493 : Vertex) [(431 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 114 = false := by
  rw [value93, value104, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 93 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value93, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 104 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value104, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (481 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 231 = true ∨ valuation q 93 = true ∨ valuation q 111 = true ∨ valuation q 114 = true := by
  rw [value93, value111, value112, value114, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(433 : Vertex), (496 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (481 : Vertex) [(433 : Vertex), (496 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 231 = true ∨ valuation q 93 = true ∨ valuation q 104 = true ∨ valuation q 111 = true := by
  rw [value93, value104, value111, value112, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(433 : Vertex), (481 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (499 : Vertex) [(433 : Vertex), (481 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 111 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value111, value113, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (496 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 232 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value111, value113, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(496 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (499 : Vertex) [(496 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 232 = true ∨ valuation q 111 = true ∨ valuation q 114 = true := by
  rw [value111, value113, value114, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(496 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (502 : Vertex) [(496 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 233 = true ∨ valuation q 112 = true ∨ valuation q 113 = true := by
  rw [value112, value113, value114, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(497 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (435 : Vertex) [(497 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 233 = true ∨ valuation q 94 = true ∨ valuation q 113 = true := by
  rw [value94, value113, value114, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(435 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (497 : Vertex) [(435 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 233 = true ∨ valuation q 94 = true ∨ valuation q 112 = true := by
  rw [value94, value112, value114, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(435 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (498 : Vertex) [(435 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 234 = true ∨ valuation q 113 = true ∨ valuation q 119 = true := by
  rw [value113, value115, value119, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (486 : Vertex) [(498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 234 = true ∨ valuation q 106 = true ∨ valuation q 119 = true := by
  rw [value106, value115, value119, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(486 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (498 : Vertex) [(486 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 75 = false ∨ valuation q 98 = false := by
  rw [value75, value98, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (504 : Vertex) (376 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 75 = false ∨ valuation q 107 = false := by
  rw [value75, value107, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (504 : Vertex) (376 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 75 = false ∨ valuation q 111 = false := by
  rw [value75, value111, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (504 : Vertex) (376 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 75 = false ∨ valuation q 117 = false := by
  rw [value75, value117, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (504 : Vertex) (376 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value98, value107, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (504 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E187.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112187
