import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 231 = true ∨ valuation q 112 = true ∨ valuation q 120 = true := by
  rw [value111, value112, value120, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(495 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (492 : Vertex) [(495 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 231 = true ∨ valuation q 110 = true ∨ valuation q 120 = true := by
  rw [value110, value111, value120, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(492 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (495 : Vertex) [(492 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 231 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value110, value111, value112, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(492 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (509 : Vertex) [(492 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 112 = true := by
  rw [value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (495 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 108 = true ∨ valuation q 111 = true := by
  rw [value108, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ∈ [(487 : Vertex), (493 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (495 : Vertex) [(487 : Vertex), (493 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 111 = true := by
  rw [value111, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(493 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (487 : Vertex) [(493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 108 = true := by
  rw [value108, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(487 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (493 : Vertex) [(487 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value106, value113, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value106, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (499 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 106 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value106, value113, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (502 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value113, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (499 : Vertex) (502 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 233 = true ∨ valuation q 106 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value106, value113, value114, value117, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(482 : Vertex), (499 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (502 : Vertex) [(482 : Vertex), (499 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 233 = true ∨ valuation q 106 = true ∨ valuation q 114 = true ∨ valuation q 116 = true := by
  rw [value106, value113, value114, value116, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(482 : Vertex), (499 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (506 : Vertex) [(482 : Vertex), (499 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 68 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value68, value113, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (498 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 95 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value95, value107, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (483 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value107, value113, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (483 : Vertex) (498 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 234 = true ∨ valuation q 95 = true ∨ valuation q 107 = true ∨ valuation q 113 = true ∨ valuation q 118 = true := by
  rw [value95, value107, value113, value114, value118, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(435 : Vertex), (483 : Vertex), (498 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (243 : Vertex) [(435 : Vertex), (483 : Vertex), (498 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value116, value119, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (500 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 235 = true ∨ valuation q 119 = true := by
  rw [value115, value119, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(508 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (502 : Vertex) [(508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 235 = true ∨ valuation q 116 = true := by
  rw [value115, value116, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(502 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (508 : Vertex) [(502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 236 = true ∨ valuation q 115 = true := by
  rw [value115, value116, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(500 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (498 : Vertex) [(500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 236 = true ∨ valuation q 113 = true := by
  rw [value113, value116, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(498 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (500 : Vertex) [(498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 100 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value100, value113, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (442 : Vertex) (498 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 237 = true ∨ valuation q 113 = true ∨ valuation q 118 = true := by
  rw [value113, value117, value118, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(498 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (442 : Vertex) [(498 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 237 = true ∨ valuation q 100 = true ∨ valuation q 118 = true := by
  rw [value100, value117, value118, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(442 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (498 : Vertex) [(442 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 237 = true ∨ valuation q 100 = true ∨ valuation q 113 = true := by
  rw [value100, value113, value117, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(442 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (507 : Vertex) [(442 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 118 = true := by
  rw [value118, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (507 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 83 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value83, value101, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 83 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value83, value101, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 83 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value83, value114, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (499 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 101 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value101, value114, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (443 : Vertex) (499 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 238 = true ∨ valuation q 101 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value101, value114, value117, value118, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(443 : Vertex), (499 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (379 : Vertex) [(443 : Vertex), (499 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block23 (q : Snake 81) (h : Conditions q) : B112E004.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112004
