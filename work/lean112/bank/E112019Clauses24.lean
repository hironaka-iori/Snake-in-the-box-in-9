import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 235 = true ∨ valuation q 102 = true ∨ valuation q 112 = true ∨ valuation q 118 = true := by
  rw [value102, value112, value114, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(451 : Vertex), (465 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (466 : Vertex) [(451 : Vertex), (465 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 235 = true ∨ valuation q 102 = true ∨ valuation q 112 = true ∨ valuation q 113 = true := by
  rw [value102, value112, value113, value114, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(451 : Vertex), (465 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (475 : Vertex) [(451 : Vertex), (465 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 115 = true := by
  rw [value115, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (468 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 50 = true ∨ valuation q 111 = true ∨ valuation q 119 = true := by
  rw [value50, value111, value115, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ∈ [(212 : Vertex), (464 : Vertex), (476 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (468 : Vertex) [(212 : Vertex), (464 : Vertex), (476 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 50 = false ∨ valuation q 111 = false := by
  rw [value50, value111, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (468 : Vertex) (212 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide)

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 50 = false ∨ valuation q 119 = false := by
  rw [value50, value119, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (468 : Vertex) (212 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide)

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 236 = true ∨ valuation q 111 = true ∨ valuation q 119 = true := by
  rw [value111, value115, value119, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(464 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (212 : Vertex) [(464 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 236 = true ∨ valuation q 50 = true ∨ valuation q 119 = true := by
  rw [value50, value115, value119, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(212 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (464 : Vertex) [(212 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 236 = true ∨ valuation q 50 = true ∨ valuation q 111 = true := by
  rw [value50, value111, value115, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(212 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (476 : Vertex) [(212 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 116 = true := by
  rw [value116, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (472 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = true ∨ valuation q 94 = true ∨ valuation q 105 = true ∨ valuation q 111 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value74, value94, value105, value111, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ∈ [(344 : Vertex), (408 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (472 : Vertex) [(344 : Vertex), (408 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value74, value94, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (408 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 94 = false ∨ valuation q 117 = false := by
  rw [value74, value94, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (408 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 94 = false ∨ valuation q 119 = false := by
  rw [value74, value94, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (408 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 105 = false ∨ valuation q 117 = false := by
  rw [value74, value105, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (456 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 105 = false ∨ valuation q 119 = false := by
  rw [value74, value105, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (456 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value74, value111, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 94 = false ∨ valuation q 105 = false ∨ valuation q 119 = false := by
  rw [value94, value105, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (408 : Vertex) (456 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 94 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value94, value111, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (408 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 111 = false ∨ valuation q 117 = false ∨ valuation q 119 = false := by
  rw [value111, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (464 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 237 = true ∨ valuation q 94 = true ∨ valuation q 105 = true ∨ valuation q 111 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value94, value105, value111, value116, value117, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(408 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (344 : Vertex) [(408 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 237 = true ∨ valuation q 74 = true ∨ valuation q 105 = true ∨ valuation q 111 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value74, value105, value111, value116, value117, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(344 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (408 : Vertex) [(344 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 237 = true ∨ valuation q 74 = true ∨ valuation q 94 = true ∨ valuation q 111 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value74, value94, value111, value116, value117, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(344 : Vertex), (408 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (456 : Vertex) [(344 : Vertex), (408 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 237 = true ∨ valuation q 74 = true ∨ valuation q 94 = true ∨ valuation q 105 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value74, value94, value105, value116, value117, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(344 : Vertex), (408 : Vertex), (456 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(344 : Vertex), (408 : Vertex), (456 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 237 = true ∨ valuation q 74 = true ∨ valuation q 94 = true ∨ valuation q 105 = true ∨ valuation q 111 = true ∨ valuation q 119 = true := by
  rw [value74, value94, value105, value111, value116, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(344 : Vertex), (408 : Vertex), (456 : Vertex), (464 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (474 : Vertex) [(344 : Vertex), (408 : Vertex), (456 : Vertex), (464 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 237 = true ∨ valuation q 74 = true ∨ valuation q 94 = true ∨ valuation q 105 = true ∨ valuation q 111 = true ∨ valuation q 117 = true := by
  rw [value74, value94, value105, value111, value116, value117, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(344 : Vertex), (408 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (476 : Vertex) [(344 : Vertex), (408 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 76 = false ∨ valuation q 113 = false := by
  rw [value55, value76, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 76 = false ∨ valuation q 116 = false := by
  rw [value55, value76, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 76 = false ∨ valuation q 118 = false := by
  rw [value55, value76, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 76 = false ∨ valuation q 120 = false := by
  rw [value55, value76, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value55, value113, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value55, value113, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E019.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112019
