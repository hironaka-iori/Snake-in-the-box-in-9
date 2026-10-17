import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value94, value96, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (359 : Vertex) (365 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 119 = false := by
  rw [value94, value96, value98, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (359 : Vertex) (365 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 119 = false := by
  rw [value94, value96, value100, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (359 : Vertex) (373 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 98 = false ∨ valuation q 100 = false ∨ valuation q 119 = false := by
  rw [value94, value98, value100, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (365 : Vertex) (373 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 21 = true ∨ valuation q 96 = true := by
  rw [value21, value95, value96, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(102 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (326 : Vertex) [(102 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 21 = true ∨ valuation q 82 = true := by
  rw [value21, value82, value95, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(102 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (359 : Vertex) [(102 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 77 = false ∨ valuation q 93 = false := by
  rw [value22, value77, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (295 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 77 = false ∨ valuation q 99 = false := by
  rw [value22, value77, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (295 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 93 = false ∨ valuation q 99 = false := by
  rw [value22, value93, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (355 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value22, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 83 = false ∨ valuation q 101 = false := by
  rw [value77, value83, value96, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (327 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 93 = false ∨ valuation q 99 = false := by
  rw [value77, value93, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (355 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value77, value93, value96, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (355 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 93 = false ∨ valuation q 120 = false := by
  rw [value77, value93, value96, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (355 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value77, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 120 = false := by
  rw [value77, value96, value99, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (367 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 101 = false ∨ valuation q 120 = false := by
  rw [value77, value96, value101, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (375 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 83 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value83, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (327 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 93 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value93, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (355 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 93 = false ∨ valuation q 99 = false ∨ valuation q 120 = false := by
  rw [value93, value96, value99, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (355 : Vertex) (367 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value94, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (357 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 95 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value95, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (358 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 120 = false := by
  rw [value96, value99, value101, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (367 : Vertex) (375 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 86 = true := by
  rw [value86, value97, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(330 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (490 : Vertex) [(330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 98 = true := by
  rw [value98, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (365 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = true ∨ valuation q 94 = true ∨ valuation q 99 = true ∨ valuation q 125 = true := by
  rw [value87, value94, value98, value99, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ∈ [(333 : Vertex), (357 : Vertex), (367 : Vertex), (493 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (365 : Vertex) [(333 : Vertex), (357 : Vertex), (367 : Vertex), (493 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 94 = true ∨ valuation q 99 = true ∨ valuation q 125 = true := by
  rw [value94, value98, value99, value125, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(357 : Vertex), (367 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (333 : Vertex) [(357 : Vertex), (367 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 87 = true ∨ valuation q 94 = true ∨ valuation q 125 = true := by
  rw [value87, value94, value98, value125, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(333 : Vertex), (357 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (367 : Vertex) [(333 : Vertex), (357 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 87 = true ∨ valuation q 94 = true ∨ valuation q 99 = true := by
  rw [value87, value94, value98, value99, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(333 : Vertex), (357 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (493 : Vertex) [(333 : Vertex), (357 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 126 = false := by
  rw [value96, value98, value99, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (359 : Vertex) (365 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 98 = true ∨ valuation q 126 = true := by
  rw [value98, value99, value126, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(365 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (359 : Vertex) [(365 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 96 = true ∨ valuation q 126 = true := by
  rw [value96, value99, value126, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(359 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (365 : Vertex) [(359 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block20 (q : Snake 81) (h : Conditions q) : B112E260.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112260
