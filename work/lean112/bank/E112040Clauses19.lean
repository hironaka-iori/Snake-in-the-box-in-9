import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value38, value106, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (376 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 38 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value38, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (379 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value88, value99, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (362 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value88, value99, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 111 = false := by
  rw [value88, value99, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (362 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value88, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (376 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value88, value106, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (376 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value88, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (379 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 99 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value99, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (362 : Vertex) (376 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 99 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value99, value106, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (362 : Vertex) (376 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 99 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value99, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (362 : Vertex) (379 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value106, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (376 : Vertex) (379 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value89, value100, value103, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (315 : Vertex) (363 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 119 = false := by
  rw [value89, value100, value109, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (315 : Vertex) (363 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value100, value103, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (363 : Vertex) (371 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 108 = false := by
  rw [value100, value103, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (363 : Vertex) (371 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 100 = false ∨ valuation q 108 = false ∨ valuation q 119 = false := by
  rw [value100, value108, value109, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (363 : Vertex) (378 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value103, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (371 : Vertex) (377 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 119 = false := by
  rw [value107, value108, value109, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (377 : Vertex) (378 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 229 = true ∨ valuation q 100 = true ∨ valuation q 103 = true ∨ valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 119 = true := by
  rw [value100, value103, value107, value108, value109, value119, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(363 : Vertex), (371 : Vertex), (377 : Vertex), (378 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (315 : Vertex) [(363 : Vertex), (371 : Vertex), (377 : Vertex), (378 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 229 = true ∨ valuation q 89 = true ∨ valuation q 103 = true ∨ valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 119 = true := by
  rw [value89, value103, value107, value108, value109, value119, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(315 : Vertex), (371 : Vertex), (377 : Vertex), (378 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (363 : Vertex) [(315 : Vertex), (371 : Vertex), (377 : Vertex), (378 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 229 = true ∨ valuation q 89 = true ∨ valuation q 100 = true ∨ valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 119 = true := by
  rw [value89, value100, value107, value108, value109, value119, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(315 : Vertex), (363 : Vertex), (377 : Vertex), (378 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (371 : Vertex) [(315 : Vertex), (363 : Vertex), (377 : Vertex), (378 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 40 = false ∨ valuation q 91 = false ∨ valuation q 107 = false := by
  rw [value40, value91, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (317 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 40 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value40, value104, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (125 : Vertex) (373 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 91 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value91, value104, value107, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (317 : Vertex) (373 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 230 = true ∨ valuation q 91 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value91, value104, value107, value110, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(317 : Vertex), (373 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (125 : Vertex) [(317 : Vertex), (373 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 230 = true ∨ valuation q 40 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value40, value104, value107, value110, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(125 : Vertex), (373 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (317 : Vertex) [(125 : Vertex), (373 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 230 = true ∨ valuation q 40 = true ∨ valuation q 91 = true ∨ valuation q 107 = true := by
  rw [value40, value91, value107, value110, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(125 : Vertex), (317 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (373 : Vertex) [(125 : Vertex), (317 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 41 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value41, value101, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (382 : Vertex) (126 : Vertex) (366 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 231 = true ∨ valuation q 101 = true ∨ valuation q 108 = true := by
  rw [value101, value108, value111, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(366 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (126 : Vertex) [(366 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 231 = true ∨ valuation q 41 = true ∨ valuation q 108 = true := by
  rw [value41, value108, value111, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(126 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (366 : Vertex) [(126 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 231 = true ∨ valuation q 41 = true ∨ valuation q 101 = true := by
  rw [value41, value101, value111, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(126 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (378 : Vertex) [(126 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E040.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112040
