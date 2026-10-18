import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 34 = false ∨ valuation q 92 = false ∨ valuation q 99 = false := by
  rw [value34, value92, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 83 = false ∨ valuation q 92 = false ∨ valuation q 99 = false := by
  rw [value83, value92, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 34 = false ∨ valuation q 83 = false := by
  rw [value34, value83, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 215 = true ∨ valuation q 83 = true ∨ valuation q 92 = true ∨ valuation q 99 = true := by
  rw [value83, value92, value93, value99, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(419 : Vertex), (433 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (307 : Vertex) [(419 : Vertex), (433 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 215 = true ∨ valuation q 34 = true ∨ valuation q 83 = true ∨ valuation q 99 = true := by
  rw [value34, value83, value93, value99, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(307 : Vertex), (419 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (433 : Vertex) [(307 : Vertex), (419 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 215 = true ∨ valuation q 34 = true ∨ valuation q 83 = true ∨ valuation q 92 = true := by
  rw [value34, value83, value92, value93, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(307 : Vertex), (419 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (443 : Vertex) [(307 : Vertex), (419 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value75, value91, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (404 : Vertex) (432 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 119 = false := by
  rw [value75, value91, value94, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (404 : Vertex) (432 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 75 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value75, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (404 : Vertex) (437 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 100 = false := by
  rw [value92, value94, value95, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (433 : Vertex) (436 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 217 = true ∨ valuation q 94 = true ∨ valuation q 100 = true := by
  rw [value94, value95, value100, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(436 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (433 : Vertex) [(436 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 217 = true ∨ valuation q 92 = true ∨ valuation q 94 = true := by
  rw [value92, value94, value95, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(433 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (445 : Vertex) [(433 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 36 = false ∨ valuation q 94 = false ∨ valuation q 101 = false := by
  rw [value36, value94, value96, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (438 : Vertex) (310 : Vertex) (436 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 218 = true ∨ valuation q 94 = true ∨ valuation q 101 = true := by
  rw [value94, value96, value101, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(436 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (310 : Vertex) [(436 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 219 = true ∨ valuation q 91 = true ∨ valuation q 98 = true ∨ valuation q 120 = true := by
  rw [value91, value97, value98, value120, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (312 : Vertex) → w ∈ [(432 : Vertex), (442 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (312 : Vertex) [(432 : Vertex), (442 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 219 = true ∨ valuation q 37 = true ∨ valuation q 98 = true ∨ valuation q 120 = true := by
  rw [value37, value97, value98, value120, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(312 : Vertex), (442 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (432 : Vertex) [(312 : Vertex), (442 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 219 = true ∨ valuation q 37 = true ∨ valuation q 91 = true ∨ valuation q 120 = true := by
  rw [value37, value91, value97, value120, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(312 : Vertex), (432 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(312 : Vertex), (432 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 219 = true ∨ valuation q 37 = true ∨ valuation q 91 = true ∨ valuation q 98 = true := by
  rw [value37, value91, value97, value98, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(312 : Vertex), (432 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (504 : Vertex) [(312 : Vertex), (432 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 78 = false ∨ valuation q 87 = false := by
  rw [value38, value78, value87, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (410 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 78 = false ∨ valuation q 97 = false := by
  rw [value38, value78, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (410 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 78 = false ∨ valuation q 99 = false := by
  rw [value38, value78, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (410 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 78 = false ∨ valuation q 101 = false := by
  rw [value38, value78, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (410 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 87 = false ∨ valuation q 97 = false := by
  rw [value38, value87, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 87 = false ∨ valuation q 99 = false := by
  rw [value38, value87, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 87 = false ∨ valuation q 101 = false := by
  rw [value38, value87, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 87 = false ∨ valuation q 121 = false := by
  rw [value38, value87, value98, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (426 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 97 = false ∨ valuation q 99 = false := by
  rw [value38, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value38, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value38, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 101 = false ∨ valuation q 121 = false := by
  rw [value38, value98, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 87 = false ∨ valuation q 97 = false := by
  rw [value78, value87, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 87 = false ∨ valuation q 99 = false := by
  rw [value78, value87, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E254.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112254
