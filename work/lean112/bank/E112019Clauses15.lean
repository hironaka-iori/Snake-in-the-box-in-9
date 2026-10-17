import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 84 = false ∨ valuation q 109 = false := by
  rw [value84, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (398 : Vertex) (390 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 86 = false ∨ valuation q 109 = false := by
  rw [value86, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (398 : Vertex) (394 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 88 = false ∨ valuation q 109 = false := by
  rw [value88, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (398 : Vertex) (396 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 210 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 109 = true := by
  rw [value86, value88, value89, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(394 : Vertex), (396 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (390 : Vertex) [(394 : Vertex), (396 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 210 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 109 = true := by
  rw [value84, value88, value89, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(390 : Vertex), (396 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (394 : Vertex) [(390 : Vertex), (396 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 210 = true ∨ valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 109 = true := by
  rw [value84, value86, value89, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (396 : Vertex) [(390 : Vertex), (394 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 210 = true ∨ valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 88 = true := by
  rw [value84, value86, value88, value89, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (462 : Vertex) [(390 : Vertex), (394 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 81 = false ∨ valuation q 92 = false ∨ valuation q 113 = false := by
  rw [value81, value90, value92, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (406 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 211 = true ∨ valuation q 92 = true ∨ valuation q 113 = true := by
  rw [value90, value92, value113, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(406 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (386 : Vertex) [(406 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 211 = true ∨ valuation q 81 = true ∨ valuation q 113 = true := by
  rw [value81, value90, value113, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(386 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (406 : Vertex) [(386 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 91 = true := by
  rw [value91, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (405 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 83 = true ∨ valuation q 93 = true ∨ valuation q 97 = true := by
  rw [value83, value91, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ∈ [(389 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (405 : Vertex) [(389 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 83 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value83, value91, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 83 = false ∨ valuation q 93 = false := by
  rw [value83, value93, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (405 : Vertex) (389 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 83 = false ∨ valuation q 97 = false := by
  rw [value83, value97, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (405 : Vertex) (389 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 212 = true ∨ valuation q 93 = true ∨ valuation q 97 = true := by
  rw [value91, value93, value97, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (389 : Vertex) [(407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 212 = true ∨ valuation q 83 = true ∨ valuation q 97 = true := by
  rw [value83, value91, value97, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(389 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (407 : Vertex) [(389 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 212 = true ∨ valuation q 83 = true ∨ valuation q 93 = true := by
  rw [value83, value91, value93, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (413 : Vertex) [(389 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 92 = true := by
  rw [value92, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (406 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 84 = true ∨ valuation q 90 = true ∨ valuation q 93 = true := by
  rw [value84, value90, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ∈ [(390 : Vertex), (402 : Vertex), (407 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (406 : Vertex) [(390 : Vertex), (402 : Vertex), (407 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 213 = true ∨ valuation q 90 = true ∨ valuation q 93 = true := by
  rw [value90, value92, value93, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(402 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (390 : Vertex) [(402 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 213 = true ∨ valuation q 84 = true ∨ valuation q 93 = true := by
  rw [value84, value92, value93, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(390 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (402 : Vertex) [(390 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 213 = true ∨ valuation q 84 = true ∨ valuation q 90 = true := by
  rw [value84, value90, value92, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(390 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (407 : Vertex) [(390 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 98 = false := by
  rw [value91, value92, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (405 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 214 = true ∨ valuation q 92 = true ∨ valuation q 98 = true := by
  rw [value92, value93, value98, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(406 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (405 : Vertex) [(406 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 214 = true ∨ valuation q 91 = true ∨ valuation q 98 = true := by
  rw [value91, value93, value98, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(405 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (406 : Vertex) [(405 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 36 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value36, value85, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 36 = false ∨ valuation q 85 = false ∨ valuation q 116 = false := by
  rw [value36, value85, value94, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (392 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 36 = false ∨ valuation q 95 = false ∨ valuation q 116 = false := by
  rw [value36, value94, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 85 = false ∨ valuation q 95 = false ∨ valuation q 116 = false := by
  rw [value85, value94, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 215 = true ∨ valuation q 36 = true ∨ valuation q 95 = true ∨ valuation q 116 = true := by
  rw [value36, value94, value95, value116, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (408 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(152 : Vertex), (409 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (408 : Vertex) (392 : Vertex) [(152 : Vertex), (409 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 215 = true ∨ valuation q 36 = true ∨ valuation q 85 = true ∨ valuation q 95 = true := by
  rw [value36, value85, value94, value95, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (408 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(152 : Vertex), (392 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (408 : Vertex) (472 : Vertex) [(152 : Vertex), (392 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E019.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112019
