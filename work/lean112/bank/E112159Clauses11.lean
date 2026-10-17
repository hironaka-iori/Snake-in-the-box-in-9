import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 222 = true ∨ valuation q 34 = true ∨ valuation q 109 = true := by
  rw [value34, value104, value109, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (484 : Vertex) → w ∈ [(229 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (485 : Vertex) (484 : Vertex) [(229 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 222 = true ∨ valuation q 34 = true ∨ valuation q 103 = true := by
  rw [value34, value103, value104, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(229 : Vertex), (484 : Vertex)] := by decide
  have hg := other_cover q (485 : Vertex) (493 : Vertex) [(229 : Vertex), (484 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 224 = true ∨ valuation q 107 = true := by
  rw [value106, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(491 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (482 : Vertex) [(491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 224 = true ∨ valuation q 102 = true := by
  rw [value102, value106, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(482 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (491 : Vertex) [(482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 39 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value39, value106, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (490 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 40 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value40, value108, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (493 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 41 = false ∨ valuation q 104 = false ∨ valuation q 108 = false := by
  rw [value41, value104, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (485 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 41 = true ∨ valuation q 108 = true := by
  rw [value41, value108, value109, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(237 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (485 : Vertex) [(237 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 228 = true ∨ valuation q 111 = true := by
  rw [value110, value111, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(497 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (480 : Vertex) [(497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value110, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (496 : Vertex) (499 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 112 = true ∨ valuation q 114 = true := by
  rw [value111, value112, value114, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(499 : Vertex), (505 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (496 : Vertex) [(499 : Vertex), (505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value111, value112, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (497 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 230 = true ∨ valuation q 111 = true ∨ valuation q 115 = true := by
  rw [value111, value112, value115, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(497 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (503 : Vertex) [(497 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 96 = true ∨ valuation q 112 = true ∨ valuation q 118 = true := by
  rw [value96, value112, value113, value118, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(439 : Vertex), (499 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (247 : Vertex) [(439 : Vertex), (499 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 47 = true ∨ valuation q 112 = true ∨ valuation q 118 = true := by
  rw [value47, value112, value113, value118, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(247 : Vertex), (499 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (439 : Vertex) [(247 : Vertex), (499 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 47 = true ∨ valuation q 96 = true ∨ valuation q 118 = true := by
  rw [value47, value96, value113, value118, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(247 : Vertex), (439 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (499 : Vertex) [(247 : Vertex), (439 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 47 = true ∨ valuation q 96 = true ∨ valuation q 112 = true := by
  rw [value47, value96, value112, value113, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(247 : Vertex), (439 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (511 : Vertex) [(247 : Vertex), (439 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 81 = false ∨ valuation q 98 = false := by
  rw [value49, value81, value98, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (249 : Vertex) (377 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 98 = false ∨ valuation q 111 = false := by
  rw [value49, value98, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (249 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value49, value98, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (249 : Vertex) (441 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value49, value111, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (249 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 81 = false ∨ valuation q 98 = false ∨ valuation q 111 = false := by
  rw [value81, value98, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (377 : Vertex) (441 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 81 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value81, value98, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (377 : Vertex) (441 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 81 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value81, value111, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (377 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 98 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value98, value111, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (441 : Vertex) (497 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 107 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value107, value112, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (491 : Vertex) (499 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 107 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value107, value112, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (491 : Vertex) (499 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 107 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value107, value114, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (491 : Vertex) (505 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 233 = true ∨ valuation q 107 = true ∨ valuation q 114 = true ∨ valuation q 118 = true := by
  rw [value107, value114, value115, value118, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(491 : Vertex), (505 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (499 : Vertex) [(491 : Vertex), (505 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 233 = true ∨ valuation q 107 = true ∨ valuation q 112 = true ∨ valuation q 118 = true := by
  rw [value107, value112, value115, value118, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(491 : Vertex), (499 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (505 : Vertex) [(491 : Vertex), (499 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 51 = false ∨ valuation q 108 = false ∨ valuation q 117 = false := by
  rw [value51, value108, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (252 : Vertex) (492 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 234 = true ∨ valuation q 51 = true ∨ valuation q 108 = true := by
  rw [value51, value108, value116, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(252 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (510 : Vertex) [(252 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E159.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112159
