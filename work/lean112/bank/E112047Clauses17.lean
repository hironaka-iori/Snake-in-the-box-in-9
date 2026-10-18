import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 57 = true ∨ valuation q 94 = true ∨ valuation q 114 = true := by
  rw [value57, value93, value94, value114, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(278 : Vertex), (407 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (390 : Vertex) [(278 : Vertex), (407 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 57 = true ∨ valuation q 83 = true ∨ valuation q 114 = true := by
  rw [value57, value83, value93, value114, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(278 : Vertex), (390 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (407 : Vertex) [(278 : Vertex), (390 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 211 = true ∨ valuation q 57 = true ∨ valuation q 83 = true ∨ valuation q 94 = true := by
  rw [value57, value83, value93, value94, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(278 : Vertex), (390 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (470 : Vertex) [(278 : Vertex), (390 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 84 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value84, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 84 = false ∨ valuation q 91 = false ∨ valuation q 93 = false := by
  rw [value84, value91, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 84 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value84, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value91, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (403 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 91 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value91, value92, value93, value94, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(403 : Vertex), (405 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (391 : Vertex) [(403 : Vertex), (405 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value84, value92, value93, value94, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(391 : Vertex), (405 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (403 : Vertex) [(391 : Vertex), (405 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 91 = true ∨ valuation q 93 = true := by
  rw [value84, value91, value93, value94, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(391 : Vertex), (403 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (405 : Vertex) [(391 : Vertex), (403 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 91 = true ∨ valuation q 92 = true := by
  rw [value84, value91, value92, value94, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(391 : Vertex), (403 : Vertex), (405 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (406 : Vertex) [(391 : Vertex), (403 : Vertex), (405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 58 = false ∨ valuation q 85 = false ∨ valuation q 96 = false := by
  rw [value58, value85, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 58 = false ∨ valuation q 85 = false ∨ valuation q 97 = false := by
  rw [value58, value85, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (392 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 58 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value58, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 58 = false ∨ valuation q 96 = false ∨ valuation q 115 = false := by
  rw [value58, value95, value96, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 58 = false ∨ valuation q 97 = false ∨ valuation q 115 = false := by
  rw [value58, value95, value97, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 85 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value85, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 85 = false ∨ valuation q 96 = false ∨ valuation q 115 = false := by
  rw [value85, value95, value96, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 85 = false ∨ valuation q 97 = false ∨ valuation q 115 = false := by
  rw [value85, value95, value97, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 115 = false := by
  rw [value95, value96, value97, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value86, value90, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value86, value95, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (408 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value86, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 95 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value95, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (408 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value90, value95, value96, value98, value99, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(401 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (393 : Vertex) [(401 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 86 = true ∨ valuation q 95 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value86, value95, value96, value98, value99, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(393 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(393 : Vertex), (408 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value86, value90, value96, value98, value99, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (408 : Vertex) [(393 : Vertex), (401 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 99 = true := by
  rw [value86, value90, value95, value96, value99, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex), (408 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(393 : Vertex), (401 : Vertex), (408 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value86, value90, value95, value96, value98, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex), (408 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (413 : Vertex) [(393 : Vertex), (401 : Vertex), (408 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 97 = true := by
  rw [value97, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (410 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 29 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value29, value87, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ∈ [(154 : Vertex), (394 : Vertex), (408 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (410 : Vertex) [(154 : Vertex), (394 : Vertex), (408 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 29 = false ∨ valuation q 87 = false ∨ valuation q 95 = false := by
  rw [value29, value87, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (394 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E047.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112047
