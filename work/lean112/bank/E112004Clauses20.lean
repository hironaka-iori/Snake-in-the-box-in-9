import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 217 = true ∨ valuation q 49 = true ∨ valuation q 88 = true ∨ valuation q 95 = true := by
  rw [value49, value88, value95, value97, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(183 : Vertex), (423 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (437 : Vertex) [(183 : Vertex), (423 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 89 = true ∨ valuation q 94 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value89, value94, value98, value99, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(424 : Vertex), (432 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (184 : Vertex) [(424 : Vertex), (432 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 50 = true ∨ valuation q 94 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value50, value94, value98, value99, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(184 : Vertex), (432 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(184 : Vertex), (432 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 50 = true ∨ valuation q 89 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value50, value89, value98, value99, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (432 : Vertex) [(184 : Vertex), (424 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 50 = true ∨ valuation q 89 = true ∨ valuation q 94 = true ∨ valuation q 100 = true := by
  rw [value50, value89, value94, value98, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (432 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (441 : Vertex) [(184 : Vertex), (424 : Vertex), (432 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 50 = true ∨ valuation q 89 = true ∨ valuation q 94 = true ∨ valuation q 99 = true := by
  rw [value50, value89, value94, value98, value99, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (432 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(184 : Vertex), (424 : Vertex), (432 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value51, value90, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (185 : Vertex) (425 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 90 = false ∨ valuation q 101 = false := by
  rw [value51, value90, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (185 : Vertex) (425 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 90 = false ∨ valuation q 102 = false := by
  rw [value51, value90, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (185 : Vertex) (425 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value51, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (185 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value51, value98, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (185 : Vertex) (440 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 51 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value51, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (185 : Vertex) (443 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value90, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (425 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value90, value98, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (425 : Vertex) (440 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 90 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value90, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (425 : Vertex) (443 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value98, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (440 : Vertex) (443 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value51, value102, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (441 : Vertex) (185 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 91 = false ∨ valuation q 98 = false := by
  rw [value52, value91, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value52, value91, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value52, value91, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 91 = false ∨ valuation q 117 = false := by
  rw [value52, value91, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value52, value98, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value52, value98, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 98 = false ∨ valuation q 117 = false := by
  rw [value52, value98, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value52, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value52, value100, value101, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 52 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value52, value100, value103, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 91 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value91, value98, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 91 = false ∨ valuation q 98 = false ∨ valuation q 103 = false := by
  rw [value91, value98, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 91 = false ∨ valuation q 98 = false ∨ valuation q 117 = false := by
  rw [value91, value98, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 91 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value91, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 91 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value91, value100, value101, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E004.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112004
