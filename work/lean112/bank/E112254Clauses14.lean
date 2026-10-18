import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 29 = false ∨ valuation q 83 = false ∨ valuation q 99 = false := by
  rw [value29, value83, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 29 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value29, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (425 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 29 = false ∨ valuation q 86 = false ∨ valuation q 99 = false := by
  rw [value29, value86, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (425 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 29 = false ∨ valuation q 87 = false ∨ valuation q 99 = false := by
  rw [value29, value87, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value83, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (425 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 99 = false := by
  rw [value83, value86, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (425 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 83 = false ∨ valuation q 87 = false ∨ valuation q 99 = false := by
  rw [value83, value87, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 99 = false := by
  rw [value86, value87, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (425 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 29 = false ∨ valuation q 83 = false := by
  rw [value29, value83, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (427 : Vertex) (299 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 99 = true := by
  rw [value83, value86, value87, value88, value99, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(419 : Vertex), (425 : Vertex), (426 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (299 : Vertex) [(419 : Vertex), (425 : Vertex), (426 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 29 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 99 = true := by
  rw [value29, value83, value86, value88, value99, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(299 : Vertex), (419 : Vertex), (425 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (426 : Vertex) [(299 : Vertex), (419 : Vertex), (425 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 211 = true ∨ valuation q 100 = true := by
  rw [value89, value100, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(445 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (425 : Vertex) [(445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 211 = true ∨ valuation q 86 = true := by
  rw [value86, value89, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(425 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (445 : Vertex) [(425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 31 = false ∨ valuation q 87 = false ∨ valuation q 101 = false := by
  rw [value31, value87, value90, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 212 = true ∨ valuation q 87 = true ∨ valuation q 101 = true := by
  rw [value87, value90, value101, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(426 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (302 : Vertex) [(426 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 212 = true ∨ valuation q 31 = true ∨ valuation q 101 = true := by
  rw [value31, value90, value101, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(302 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (426 : Vertex) [(302 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 212 = true ∨ valuation q 31 = true ∨ valuation q 87 = true := by
  rw [value31, value87, value90, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(302 : Vertex), (426 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (446 : Vertex) [(302 : Vertex), (426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 32 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value32, value91, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (304 : Vertex) (433 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 32 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value32, value91, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (304 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 82 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value82, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (433 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 82 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value82, value91, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (433 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 82 = false ∨ valuation q 92 = false ∨ valuation q 117 = false := by
  rw [value82, value91, value92, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (433 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 82 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value82, value91, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 82 = false ∨ valuation q 97 = false ∨ valuation q 117 = false := by
  rw [value82, value91, value97, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (440 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value91, value92, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (433 : Vertex) (436 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 117 = false := by
  rw [value91, value92, value97, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (433 : Vertex) (440 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 117 = false := by
  rw [value91, value94, value97, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (436 : Vertex) (440 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 33 = false ∨ valuation q 91 = false ∨ valuation q 95 = false := by
  rw [value33, value91, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (432 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 214 = true ∨ valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 95 = true := by
  rw [value91, value92, value93, value95, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(432 : Vertex), (435 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (305 : Vertex) [(432 : Vertex), (435 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 214 = true ∨ valuation q 33 = true ∨ valuation q 91 = true ∨ valuation q 95 = true := by
  rw [value33, value91, value92, value95, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(305 : Vertex), (432 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (435 : Vertex) [(305 : Vertex), (432 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 34 = false ∨ valuation q 83 = false ∨ valuation q 92 = false := by
  rw [value34, value83, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 34 = false ∨ valuation q 83 = false ∨ valuation q 99 = false := by
  rw [value34, value83, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E254.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112254
