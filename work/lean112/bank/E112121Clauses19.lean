import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 69 = false ∨ valuation q 88 = false ∨ valuation q 94 = false := by
  rw [value69, value87, value88, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 69 = false ∨ valuation q 88 = false ∨ valuation q 110 = false := by
  rw [value69, value87, value88, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 69 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value69, value87, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (418 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 69 = false ∨ valuation q 89 = false ∨ valuation q 94 = false := by
  rw [value69, value87, value89, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (418 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 69 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value69, value87, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (420 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 69 = false ∨ valuation q 94 = false ∨ valuation q 110 = false := by
  rw [value69, value87, value94, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value87, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (418 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 94 = false := by
  rw [value87, value88, value89, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (418 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value87, value88, value89, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (418 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value87, value88, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (420 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value87, value88, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (420 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 94 = false ∨ valuation q 110 = false := by
  rw [value87, value88, value94, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value87, value89, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (418 : Vertex) (420 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value87, value89, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (418 : Vertex) (420 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 94 = false ∨ valuation q 110 = false := by
  rw [value87, value89, value94, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (418 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 110 = false := by
  rw [value87, value90, value94, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (420 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 45 = false ∨ valuation q 70 = false ∨ valuation q 87 = false := by
  rw [value45, value70, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 45 = false ∨ valuation q 70 = false ∨ valuation q 111 = false := by
  rw [value45, value70, value88, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 45 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value45, value87, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 45 = false ∨ valuation q 87 = false ∨ valuation q 111 = false := by
  rw [value45, value87, value88, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 45 = false ∨ valuation q 91 = false ∨ valuation q 111 = false := by
  rw [value45, value88, value91, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 70 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value70, value87, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 70 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value70, value88, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 70 = false ∨ valuation q 91 = false ∨ valuation q 111 = false := by
  rw [value70, value88, value91, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 70 = false ∨ valuation q 100 = false ∨ valuation q 111 = false := by
  rw [value70, value88, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value87, value88, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 111 = false := by
  rw [value87, value88, value91, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 111 = false := by
  rw [value88, value91, value100, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (421 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 214 = true ∨ valuation q 70 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 111 = true := by
  rw [value70, value87, value88, value91, value100, value111, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(289 : Vertex), (416 : Vertex), (421 : Vertex), (433 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (161 : Vertex) [(289 : Vertex), (416 : Vertex), (421 : Vertex), (433 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 214 = true ∨ valuation q 45 = true ∨ valuation q 70 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 111 = true := by
  rw [value45, value70, value88, value91, value100, value111, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(161 : Vertex), (289 : Vertex), (421 : Vertex), (433 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (416 : Vertex) [(161 : Vertex), (289 : Vertex), (421 : Vertex), (433 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 214 = true ∨ valuation q 45 = true ∨ valuation q 70 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 100 = true := by
  rw [value45, value70, value87, value88, value91, value100, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(161 : Vertex), (289 : Vertex), (416 : Vertex), (421 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (481 : Vertex) [(161 : Vertex), (289 : Vertex), (416 : Vertex), (421 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 215 = true ∨ valuation q 92 = true ∨ valuation q 95 = true := by
  rw [value89, value92, value95, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(422 : Vertex), (426 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (416 : Vertex) [(422 : Vertex), (426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E121.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112121
