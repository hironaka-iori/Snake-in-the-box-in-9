import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 111 = false := by
  rw [value25, value54, value91, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (273 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value25, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value25, value91, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 92 = false ∨ valuation q 111 = false := by
  rw [value25, value91, value92, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (403 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value25, value91, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 93 = false ∨ valuation q 111 = false := by
  rw [value25, value91, value93, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (405 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 97 = false ∨ valuation q 111 = false := by
  rw [value25, value91, value97, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (409 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 54 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value54, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 54 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value54, value91, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 54 = false ∨ valuation q 92 = false ∨ valuation q 111 = false := by
  rw [value54, value91, value92, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (403 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 54 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value54, value91, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 54 = false ∨ valuation q 93 = false ∨ valuation q 111 = false := by
  rw [value54, value91, value93, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (405 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 54 = false ∨ valuation q 97 = false ∨ valuation q 111 = false := by
  rw [value54, value91, value97, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (409 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value91, value92, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (403 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 111 = false := by
  rw [value91, value92, value93, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (403 : Vertex) (405 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 111 = false := by
  rw [value91, value92, value97, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (403 : Vertex) (409 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 97 = false ∨ valuation q 111 = false := by
  rw [value91, value93, value97, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (405 : Vertex) (409 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 27 = false ∨ valuation q 56 = false ∨ valuation q 95 = false := by
  rw [value27, value56, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (147 : Vertex) (275 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 56 = false ∨ valuation q 91 = false ∨ valuation q 95 = false := by
  rw [value56, value91, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (401 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 56 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value56, value91, value92, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 56 = false ∨ valuation q 91 = false ∨ valuation q 112 = false := by
  rw [value56, value91, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (401 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 56 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value56, value92, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 56 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value56, value92, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (275 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 82 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value82, value91, value92, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (387 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value91, value92, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value91, value92, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value91, value92, value99, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 93 = true := by
  rw [value93, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (405 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = true ∨ valuation q 95 = true ∨ valuation q 100 = true := by
  rw [value91, value93, value95, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ∈ [(401 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (405 : Vertex) [(401 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 95 = true ∨ valuation q 100 = true := by
  rw [value93, value95, value100, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (401 : Vertex) [(407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 91 = true ∨ valuation q 100 = true := by
  rw [value91, value93, value100, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(401 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (407 : Vertex) [(401 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 91 = true ∨ valuation q 95 = true := by
  rw [value91, value93, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(401 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (413 : Vertex) [(401 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block13 (q : Snake 81) (h : Conditions q) : B112E007.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112007
