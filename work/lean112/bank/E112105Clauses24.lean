import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value109, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value109, value111, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 124 = false := by
  rw [value109, value112, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (462 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 102 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value102, value114, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (465 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 102 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value102, value114, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (465 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 102 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value102, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value114, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value114, value115, value116, value117, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(465 : Vertex), (466 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (448 : Vertex) [(465 : Vertex), (466 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 102 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value102, value114, value116, value117, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(448 : Vertex), (466 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (465 : Vertex) [(448 : Vertex), (466 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 102 = true ∨ valuation q 115 = true ∨ valuation q 117 = true := by
  rw [value102, value114, value115, value117, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(448 : Vertex), (465 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (466 : Vertex) [(448 : Vertex), (465 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 102 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value102, value114, value115, value116, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(448 : Vertex), (465 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (468 : Vertex) [(448 : Vertex), (465 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 115 = true := by
  rw [value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (465 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 58 = true ∨ valuation q 103 = true ∨ valuation q 114 = true ∨ valuation q 118 = true := by
  rw [value58, value103, value114, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ∈ [(209 : Vertex), (449 : Vertex), (464 : Vertex), (469 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (465 : Vertex) [(209 : Vertex), (449 : Vertex), (464 : Vertex), (469 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 58 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value58, value103, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (209 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 58 = false ∨ valuation q 103 = false ∨ valuation q 118 = false := by
  rw [value58, value103, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (209 : Vertex) (449 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 58 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value58, value114, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (209 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 103 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value103, value114, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (449 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 58 = false ∨ valuation q 114 = false := by
  rw [value58, value114, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (465 : Vertex) (209 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 58 = false ∨ valuation q 118 = false := by
  rw [value58, value118, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (465 : Vertex) (209 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide)

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 103 = false ∨ valuation q 114 = false := by
  rw [value103, value114, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (465 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide)

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value114, value118, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (465 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide)

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 103 = true ∨ valuation q 114 = true ∨ valuation q 118 = true := by
  rw [value103, value114, value115, value118, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(449 : Vertex), (464 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (209 : Vertex) [(449 : Vertex), (464 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 58 = true ∨ valuation q 114 = true ∨ valuation q 118 = true := by
  rw [value58, value114, value115, value118, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(209 : Vertex), (464 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (449 : Vertex) [(209 : Vertex), (464 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 58 = true ∨ valuation q 103 = true ∨ valuation q 118 = true := by
  rw [value58, value103, value115, value118, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(209 : Vertex), (449 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (464 : Vertex) [(209 : Vertex), (449 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 58 = true ∨ valuation q 103 = true ∨ valuation q 114 = true := by
  rw [value58, value103, value114, value115, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(209 : Vertex), (449 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (469 : Vertex) [(209 : Vertex), (449 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 116 = true := by
  rw [value116, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (466 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 104 = true ∨ valuation q 114 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value104, value114, value116, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ∈ [(450 : Vertex), (464 : Vertex), (470 : Vertex), (474 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (466 : Vertex) [(450 : Vertex), (464 : Vertex), (470 : Vertex), (474 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 104 = false ∨ valuation q 114 = false ∨ valuation q 119 = false := by
  rw [value104, value114, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (450 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 104 = false ∨ valuation q 114 = false ∨ valuation q 120 = false := by
  rw [value104, value114, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (450 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 114 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value114, value116, value119, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(464 : Vertex), (470 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (450 : Vertex) [(464 : Vertex), (470 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 104 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value104, value116, value119, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(450 : Vertex), (470 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (464 : Vertex) [(450 : Vertex), (470 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 104 = true ∨ valuation q 114 = true ∨ valuation q 120 = true := by
  rw [value104, value114, value116, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(450 : Vertex), (464 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (470 : Vertex) [(450 : Vertex), (464 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block24 (q : Snake 81) (h : Conditions q) : B112E105.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112105
