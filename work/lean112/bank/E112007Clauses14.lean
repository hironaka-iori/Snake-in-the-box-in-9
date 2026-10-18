import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 95 = true ∨ valuation q 114 = true := by
  rw [value84, value94, value95, value114, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(390 : Vertex), (407 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (278 : Vertex) [(390 : Vertex), (407 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 58 = true ∨ valuation q 84 = true ∨ valuation q 95 = true := by
  rw [value58, value84, value94, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(278 : Vertex), (390 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (470 : Vertex) [(278 : Vertex), (390 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 85 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value85, value92, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 85 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value85, value92, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 85 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value85, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value92, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (403 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value92, value93, value94, value95, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(403 : Vertex), (405 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (391 : Vertex) [(403 : Vertex), (405 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 85 = true ∨ valuation q 92 = true ∨ valuation q 94 = true := by
  rw [value85, value92, value94, value95, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(391 : Vertex), (403 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (405 : Vertex) [(391 : Vertex), (403 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 59 = false ∨ valuation q 86 = false ∨ valuation q 97 = false := by
  rw [value59, value86, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 59 = false ∨ valuation q 86 = false ∨ valuation q 98 = false := by
  rw [value59, value86, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (392 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 59 = false ∨ valuation q 86 = false ∨ valuation q 115 = false := by
  rw [value59, value86, value96, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (392 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 59 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value59, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 59 = false ∨ valuation q 97 = false ∨ valuation q 115 = false := by
  rw [value59, value96, value97, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 59 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value59, value96, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value86, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 97 = false ∨ valuation q 115 = false := by
  rw [value86, value96, value97, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value86, value96, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value96, value97, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 86 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 115 = true := by
  rw [value86, value96, value97, value98, value115, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (408 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(392 : Vertex), (409 : Vertex), (410 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (408 : Vertex) (280 : Vertex) [(392 : Vertex), (409 : Vertex), (410 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value87, value91, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 87 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value87, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (408 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 87 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value87, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 91 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value91, value96, value97, value99, value100, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(401 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (393 : Vertex) [(401 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value87, value96, value97, value99, value100, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(393 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(393 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value87, value91, value97, value99, value100, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (408 : Vertex) [(393 : Vertex), (401 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 29 = true ∨ valuation q 88 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value29, value88, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ∈ [(154 : Vertex), (394 : Vertex), (408 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (410 : Vertex) [(154 : Vertex), (394 : Vertex), (408 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 29 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value29, value88, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (394 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 88 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value88, value96, value98, value99, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(394 : Vertex), (408 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (154 : Vertex) [(394 : Vertex), (408 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 29 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value29, value96, value98, value99, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(154 : Vertex), (408 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (394 : Vertex) [(154 : Vertex), (408 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 29 = true ∨ valuation q 88 = true ∨ valuation q 99 = true := by
  rw [value29, value88, value98, value99, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(154 : Vertex), (394 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (408 : Vertex) [(154 : Vertex), (394 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 29 = true ∨ valuation q 88 = true ∨ valuation q 96 = true := by
  rw [value29, value88, value96, value98, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(154 : Vertex), (394 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (411 : Vertex) [(154 : Vertex), (394 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value92, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (403 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E007.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112007
