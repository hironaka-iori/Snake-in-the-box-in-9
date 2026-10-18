import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 54 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value54, value90, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 54 = false ∨ valuation q 92 = false ∨ valuation q 110 = false := by
  rw [value54, value90, value92, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (405 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 54 = false ∨ valuation q 96 = false ∨ valuation q 110 = false := by
  rw [value54, value90, value96, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (409 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value90, value91, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (403 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 110 = false := by
  rw [value90, value91, value92, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (403 : Vertex) (405 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 96 = false ∨ valuation q 110 = false := by
  rw [value90, value91, value96, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (403 : Vertex) (409 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 96 = false ∨ valuation q 110 = false := by
  rw [value90, value92, value96, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (405 : Vertex) (409 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 91 = true := by
  rw [value91, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (403 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 27 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value27, value55, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (275 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 27 = false ∨ valuation q 55 = false ∨ valuation q 94 = false := by
  rw [value27, value55, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (275 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 27 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value27, value90, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (401 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 27 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value27, value90, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (401 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 55 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value55, value90, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (401 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 55 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value55, value90, value91, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 55 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value55, value90, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (401 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 55 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value55, value91, value94, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 55 = false ∨ valuation q 94 = false ∨ valuation q 112 = false := by
  rw [value55, value91, value94, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 55 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value55, value91, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 81 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value81, value91, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (387 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value90, value91, value94, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 112 = false := by
  rw [value90, value91, value94, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value90, value91, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value91, value94, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (407 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 92 = true := by
  rw [value92, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (405 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = true ∨ valuation q 94 = true ∨ valuation q 99 = true := by
  rw [value90, value92, value94, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ∈ [(401 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (405 : Vertex) [(401 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value90, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (405 : Vertex) (401 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 94 = true ∨ valuation q 99 = true := by
  rw [value92, value94, value99, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (401 : Vertex) [(407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 90 = true ∨ valuation q 99 = true := by
  rw [value90, value92, value99, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(401 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (407 : Vertex) [(401 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 210 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value90, value92, value94, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(401 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (413 : Vertex) [(401 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 57 = false ∨ valuation q 83 = false ∨ valuation q 94 = false := by
  rw [value57, value83, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (278 : Vertex) (390 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 83 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value83, value93, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (390 : Vertex) (407 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 83 = true ∨ valuation q 94 = true ∨ valuation q 114 = true := by
  rw [value83, value93, value94, value114, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(390 : Vertex), (407 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (278 : Vertex) [(390 : Vertex), (407 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block16 (q : Snake 81) (h : Conditions q) : B112E047.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112047
