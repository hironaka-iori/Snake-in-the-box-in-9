import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 95 = true := by
  rw [value87, value89, value95, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(416 : Vertex), (426 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (422 : Vertex) [(416 : Vertex), (426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 92 = true := by
  rw [value87, value89, value92, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(416 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (426 : Vertex) [(416 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value87, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 97 = false := by
  rw [value87, value90, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 102 = false := by
  rw [value87, value90, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 102 = false := by
  rw [value87, value90, value97, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 102 = false := by
  rw [value90, value91, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 216 = true ∨ valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 97 = true ∨ valuation q 102 = true := by
  rw [value87, value90, value92, value97, value102, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(416 : Vertex), (422 : Vertex), (428 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (421 : Vertex) [(416 : Vertex), (422 : Vertex), (428 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 216 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 92 = true ∨ valuation q 102 = true := by
  rw [value87, value90, value91, value92, value102, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(416 : Vertex), (421 : Vertex), (422 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (428 : Vertex) [(416 : Vertex), (421 : Vertex), (422 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 216 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 92 = true ∨ valuation q 97 = true := by
  rw [value87, value90, value91, value92, value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(416 : Vertex), (421 : Vertex), (422 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (436 : Vertex) [(416 : Vertex), (421 : Vertex), (422 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 46 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value46, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 46 = false ∨ valuation q 88 = false ∨ valuation q 93 = false := by
  rw [value46, value88, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 46 = false ∨ valuation q 88 = false ∨ valuation q 103 = false := by
  rw [value46, value88, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 46 = false ∨ valuation q 93 = false ∨ valuation q 103 = false := by
  rw [value46, value91, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (423 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value88, value90, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 103 = false := by
  rw [value88, value90, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 103 = false := by
  rw [value88, value91, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (423 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 103 = false := by
  rw [value90, value91, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (420 : Vertex) (423 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 217 = true ∨ valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 103 = true := by
  rw [value88, value90, value91, value93, value103, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (165 : Vertex) [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value47, value71, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 71 = false ∨ valuation q 90 = false := by
  rw [value47, value71, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 71 = false ∨ valuation q 93 = false := by
  rw [value47, value71, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 71 = false ∨ valuation q 98 = false := by
  rw [value47, value71, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 71 = false ∨ valuation q 112 = false := by
  rw [value47, value71, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (294 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value47, value89, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (418 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value47, value89, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (418 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value47, value89, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (418 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 89 = false ∨ valuation q 112 = false := by
  rw [value47, value89, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (418 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value47, value90, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value47, value90, value92, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (420 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value47, value90, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (420 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 47 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value47, value92, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E121.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112121
