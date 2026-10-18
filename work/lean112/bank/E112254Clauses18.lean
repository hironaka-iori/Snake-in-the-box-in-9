import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 239 = true ∨ valuation q 91 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value91, value117, value118, value119, value120, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(432 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (368 : Vertex) [(432 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 239 = true ∨ valuation q 57 = true ∨ valuation q 91 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value57, value91, value117, value119, value120, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(368 : Vertex), (432 : Vertex), (500 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (498 : Vertex) [(368 : Vertex), (432 : Vertex), (500 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 58 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value58, value111, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (482 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 58 = false ∨ valuation q 111 = false ∨ valuation q 121 = false := by
  rw [value58, value111, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (482 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 58 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value58, value117, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (496 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 111 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value111, value117, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (496 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 94 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value94, value117, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (436 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 241 = true ∨ valuation q 94 = true ∨ valuation q 117 = true := by
  rw [value94, value117, value119, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(436 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (508 : Vertex) [(436 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 59 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value59, value97, value114, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (376 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 59 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value59, value114, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (376 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 59 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value59, value114, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (376 : Vertex) (488 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 114 = false := by
  rw [value97, value108, value114, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (472 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 117 = false := by
  rw [value97, value108, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (472 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 121 = false := by
  rw [value97, value108, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (472 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 122 = false := by
  rw [value97, value108, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (472 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value97, value114, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value97, value114, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (488 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value97, value114, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (488 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value97, value117, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (496 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value97, value117, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 97 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value97, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (506 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 114 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value114, value117, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (488 : Vertex) (496 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 114 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value114, value117, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (488 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 114 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value114, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (488 : Vertex) (506 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 117 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value117, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (496 : Vertex) (506 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 243 = true ∨ valuation q 98 = true ∨ valuation q 118 = true ∨ valuation q 120 = true := by
  rw [value98, value118, value120, value121, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(442 : Vertex), (498 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (378 : Vertex) [(442 : Vertex), (498 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 243 = true ∨ valuation q 61 = true ∨ valuation q 98 = true ∨ valuation q 120 = true := by
  rw [value61, value98, value120, value121, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(378 : Vertex), (442 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (498 : Vertex) [(378 : Vertex), (442 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 109 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value109, value116, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (476 : Vertex) (492 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 244 = true ∨ valuation q 109 = true ∨ valuation q 116 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value109, value116, value119, value120, value122, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(476 : Vertex), (492 : Vertex), (500 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (380 : Vertex) [(476 : Vertex), (492 : Vertex), (500 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 244 = true ∨ valuation q 63 = true ∨ valuation q 116 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value63, value116, value119, value120, value122, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(380 : Vertex), (492 : Vertex), (500 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (476 : Vertex) [(380 : Vertex), (492 : Vertex), (500 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 244 = true ∨ valuation q 63 = true ∨ valuation q 109 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value63, value109, value119, value120, value122, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(380 : Vertex), (476 : Vertex), (500 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (492 : Vertex) [(380 : Vertex), (476 : Vertex), (500 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 244 = true ∨ valuation q 63 = true ∨ valuation q 109 = true ∨ valuation q 116 = true ∨ valuation q 120 = true := by
  rw [value63, value109, value116, value120, value122, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(380 : Vertex), (476 : Vertex), (492 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (500 : Vertex) [(380 : Vertex), (476 : Vertex), (492 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E254.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112254
