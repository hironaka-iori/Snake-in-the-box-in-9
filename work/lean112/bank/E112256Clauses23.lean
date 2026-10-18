import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 96 = false ∨ valuation q 120 = false ∨ valuation q 122 = false := by
  rw [value96, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (373 : Vertex) (500 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 96 = false ∨ valuation q 120 = false ∨ valuation q 126 = false := by
  rw [value96, value120, value121, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (373 : Vertex) (500 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 96 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value96, value121, value122, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (373 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 109 = false ∨ valuation q 120 = false ∨ valuation q 122 = false := by
  rw [value109, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (469 : Vertex) (500 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 109 = false ∨ valuation q 120 = false ∨ valuation q 126 = false := by
  rw [value109, value120, value121, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (469 : Vertex) (500 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 109 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value109, value121, value122, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (469 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 120 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value120, value121, value122, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (501 : Vertex) (500 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 122 = true := by
  rw [value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (503 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 97 = true ∨ valuation q 119 = true ∨ valuation q 121 = true ∨ valuation q 127 = true := by
  rw [value97, value119, value121, value122, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ∈ [(375 : Vertex), (499 : Vertex), (501 : Vertex), (511 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (503 : Vertex) [(375 : Vertex), (499 : Vertex), (501 : Vertex), (511 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 97 = false ∨ valuation q 127 = false := by
  rw [value97, value127, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (503 : Vertex) (375 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 119 = true ∨ valuation q 121 = true ∨ valuation q 127 = true := by
  rw [value119, value121, value122, value127, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(499 : Vertex), (501 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (375 : Vertex) [(499 : Vertex), (501 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 97 = true ∨ valuation q 121 = true ∨ valuation q 127 = true := by
  rw [value97, value121, value122, value127, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(375 : Vertex), (501 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (499 : Vertex) [(375 : Vertex), (501 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 97 = true ∨ valuation q 119 = true ∨ valuation q 127 = true := by
  rw [value97, value119, value122, value127, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(375 : Vertex), (499 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (501 : Vertex) [(375 : Vertex), (499 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 97 = true ∨ valuation q 119 = true ∨ valuation q 121 = true := by
  rw [value97, value119, value121, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(375 : Vertex), (499 : Vertex), (501 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (511 : Vertex) [(375 : Vertex), (499 : Vertex), (501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 70 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value70, value118, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (250 : Vertex) (498 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 70 = true ∨ valuation q 124 = true := by
  rw [value70, value123, value124, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(250 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (498 : Vertex) [(250 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 98 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value98, value123, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (506 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 113 = false ∨ valuation q 120 = false ∨ valuation q 126 = false := by
  rw [value113, value120, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (476 : Vertex) (500 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 252 = true ∨ valuation q 113 = true ∨ valuation q 126 = true := by
  rw [value113, value125, value126, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(476 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (500 : Vertex) [(476 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 99 = false ∨ valuation q 125 = false ∨ valuation q 127 = false := by
  rw [value99, value125, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (508 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 253 = true ∨ valuation q 99 = true ∨ valuation q 114 = true ∨ valuation q 121 = true ∨ valuation q 125 = true ∨ valuation q 127 = true := by
  rw [value99, value114, value121, value125, value126, value127, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (253 : Vertex) → w ∈ [(381 : Vertex), (477 : Vertex), (501 : Vertex), (508 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (509 : Vertex) (253 : Vertex) [(381 : Vertex), (477 : Vertex), (501 : Vertex), (508 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 253 = true ∨ valuation q 72 = true ∨ valuation q 99 = true ∨ valuation q 114 = true ∨ valuation q 125 = true ∨ valuation q 127 = true := by
  rw [value72, value99, value114, value125, value126, value127, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(253 : Vertex), (381 : Vertex), (477 : Vertex), (508 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (509 : Vertex) (501 : Vertex) [(253 : Vertex), (381 : Vertex), (477 : Vertex), (508 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 101 = false ∨ valuation q 116 = false ∨ valuation q 122 = false := by
  rw [value101, value116, value122, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (495 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 101 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value101, value116, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (495 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 101 = false ∨ valuation q 116 = false ∨ valuation q 126 = false := by
  rw [value101, value116, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 101 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value101, value122, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 101 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value101, value122, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 101 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value101, value124, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 116 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value116, value122, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (495 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 116 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value116, value122, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (495 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 116 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value116, value124, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (495 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 122 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value122, value124, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (503 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E256.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112256
