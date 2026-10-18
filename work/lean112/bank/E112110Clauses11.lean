import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 84 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value84, value92, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 84 = false ∨ valuation q 92 = false ∨ valuation q 115 = false := by
  rw [value84, value92, value93, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (409 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 84 = false ∨ valuation q 95 = false ∨ valuation q 115 = false := by
  rw [value84, value93, value95, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (415 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 115 = false := by
  rw [value92, value93, value95, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (409 : Vertex) (415 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 115 = true := by
  rw [value92, value93, value95, value115, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (395 : Vertex) → w ∈ [(409 : Vertex), (415 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (395 : Vertex) [(409 : Vertex), (415 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 84 = true ∨ valuation q 95 = true ∨ valuation q 115 = true := by
  rw [value84, value93, value95, value115, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(395 : Vertex), (415 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (409 : Vertex) [(395 : Vertex), (415 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 84 = true ∨ valuation q 92 = true ∨ valuation q 115 = true := by
  rw [value84, value92, value93, value115, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(395 : Vertex), (409 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (415 : Vertex) [(395 : Vertex), (409 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value88, value92, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (405 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 92 = true ∨ valuation q 95 = true := by
  rw [value92, value94, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (405 : Vertex) [(409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 88 = true ∨ valuation q 95 = true := by
  rw [value88, value94, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(405 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (409 : Vertex) [(405 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 33 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value33, value90, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 33 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value33, value90, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 33 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value33, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 33 = false ∨ valuation q 93 = false ∨ valuation q 118 = false := by
  rw [value33, value93, value95, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (411 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 118 = false := by
  rw [value90, value93, value95, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (411 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value93, value94, value95, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (411 : Vertex) (413 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 59 = false ∨ valuation q 76 = false := by
  rw [value34, value59, value76, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 59 = false ∨ valuation q 97 = false := by
  rw [value34, value59, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 59 = false ∨ valuation q 102 = false := by
  rw [value34, value59, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 59 = false ∨ valuation q 108 = false := by
  rw [value34, value59, value96, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 76 = false ∨ valuation q 97 = false := by
  rw [value34, value76, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (384 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 76 = false ∨ valuation q 98 = false := by
  rw [value34, value76, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (384 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 76 = false ∨ valuation q 108 = false := by
  rw [value34, value76, value96, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (384 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value34, value96, value97, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value34, value96, value98, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (450 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 34 = false ∨ valuation q 98 = false ∨ valuation q 108 = false := by
  rw [value34, value96, value98, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 59 = false ∨ valuation q 97 = false ∨ valuation q 102 = false := by
  rw [value59, value96, value97, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (449 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 59 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value59, value96, value97, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (320 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 60 = false ∨ valuation q 77 = false := by
  rw [value35, value60, value77, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 60 = false ∨ valuation q 99 = false := by
  rw [value35, value60, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 60 = false ∨ valuation q 100 = false := by
  rw [value35, value60, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 35 = false ∨ valuation q 60 = false ∨ valuation q 109 = false := by
  rw [value35, value60, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E110.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112110
