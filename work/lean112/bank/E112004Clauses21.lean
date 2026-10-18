import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 91 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value91, value100, value103, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value98, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value98, value100, value101, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value98, value100, value103, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value100, value101, value103, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (443 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value103, value117, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (442 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 92 = false ∨ valuation q 100 = false := by
  rw [value77, value92, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 92 = false ∨ valuation q 118 = false := by
  rw [value77, value92, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (427 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 95 = false ∨ valuation q 100 = false := by
  rw [value77, value95, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 95 = false ∨ valuation q 118 = false := by
  rw [value77, value95, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (435 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value77, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 118 = false := by
  rw [value77, value99, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (441 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value77, value100, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (442 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 100 = false := by
  rw [value92, value95, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 118 = false := by
  rw [value92, value95, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 92 = false ∨ valuation q 99 = false ∨ valuation q 118 = false := by
  rw [value92, value99, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 92 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value92, value100, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (442 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 95 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value95, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 95 = false ∨ valuation q 99 = false ∨ valuation q 118 = false := by
  rw [value95, value99, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (441 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value99, value100, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (441 : Vertex) (442 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 221 = true ∨ valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 118 = true := by
  rw [value92, value95, value99, value100, value101, value118, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (315 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 221 = true ∨ valuation q 77 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 118 = true := by
  rw [value77, value95, value99, value100, value101, value118, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(315 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (427 : Vertex) [(315 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 221 = true ∨ valuation q 77 = true ∨ valuation q 92 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 118 = true := by
  rw [value77, value92, value99, value100, value101, value118, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(315 : Vertex), (427 : Vertex), (441 : Vertex), (442 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (435 : Vertex) [(315 : Vertex), (427 : Vertex), (441 : Vertex), (442 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 221 = true ∨ valuation q 77 = true ∨ valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value77, value92, value95, value99, value100, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(315 : Vertex), (427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (507 : Vertex) [(315 : Vertex), (427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 54 = false ∨ valuation q 96 = false ∨ valuation q 120 = false := by
  rw [value54, value96, value102, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (189 : Vertex) (437 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 120 = false := by
  rw [value96, value99, value102, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (437 : Vertex) (441 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 222 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 120 = true := by
  rw [value96, value99, value102, value120, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(437 : Vertex), (441 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (189 : Vertex) [(437 : Vertex), (441 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 222 = true ∨ valuation q 54 = true ∨ valuation q 99 = true ∨ valuation q 120 = true := by
  rw [value54, value99, value102, value120, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(189 : Vertex), (441 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (437 : Vertex) [(189 : Vertex), (441 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 222 = true ∨ valuation q 54 = true ∨ valuation q 96 = true ∨ valuation q 120 = true := by
  rw [value54, value96, value102, value120, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(189 : Vertex), (437 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (441 : Vertex) [(189 : Vertex), (437 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 222 = true ∨ valuation q 54 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value54, value96, value99, value102, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(189 : Vertex), (437 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (509 : Vertex) [(189 : Vertex), (437 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 55 = false ∨ valuation q 93 = false ∨ valuation q 100 = false := by
  rw [value55, value93, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (446 : Vertex) (190 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 223 = true ∨ valuation q 93 = true ∨ valuation q 100 = true := by
  rw [value93, value100, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (190 : Vertex) [(430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block21 (q : Snake 81) (h : Conditions q) : B112E004.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112004
