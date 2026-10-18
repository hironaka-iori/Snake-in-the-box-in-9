import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value96, value113, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value96, value113, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 113 = false ∨ valuation q 127 = false := by
  rw [value96, value113, value117, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (453 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value96, value115, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 115 = false ∨ valuation q 127 = false := by
  rw [value96, value115, value117, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 96 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value96, value117, value119, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 119 = false := by
  rw [value113, value115, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 127 = false := by
  rw [value113, value115, value117, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 113 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value113, value117, value119, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (453 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 115 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value115, value117, value119, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (457 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 39 = false ∨ valuation q 97 = false ∨ valuation q 119 = false := by
  rw [value39, value97, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 39 = false ∨ valuation q 97 = false ∨ valuation q 128 = false := by
  rw [value39, value97, value118, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 39 = false ∨ valuation q 119 = false ∨ valuation q 128 = false := by
  rw [value39, value118, value119, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 97 = false ∨ valuation q 119 = false ∨ valuation q 128 = false := by
  rw [value97, value118, value119, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value114, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value114, value116, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (459 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 114 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value114, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value116, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (459 : Vertex) (461 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 247 = true ∨ valuation q 114 = true ∨ valuation q 117 = true ∨ valuation q 118 = true := by
  rw [value114, value117, value118, value119, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(455 : Vertex), (461 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (459 : Vertex) [(455 : Vertex), (461 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 247 = true ∨ valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 118 = true := by
  rw [value114, value116, value118, value119, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (461 : Vertex) [(455 : Vertex), (459 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 247 = true ∨ valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value114, value116, value117, value119, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (462 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 109 = false ∨ valuation q 121 = false ∨ valuation q 124 = false := by
  rw [value109, value120, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 248 = true ∨ valuation q 109 = true ∨ valuation q 124 = true := by
  rw [value109, value120, value124, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(448 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (466 : Vertex) [(448 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 120 = false ∨ valuation q 122 = false ∨ valuation q 125 = false := by
  rw [value120, value121, value122, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (464 : Vertex) (467 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 122 = true ∨ valuation q 125 = true := by
  rw [value121, value122, value125, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(467 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (464 : Vertex) [(467 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 120 = true ∨ valuation q 125 = true := by
  rw [value120, value121, value125, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(464 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (467 : Vertex) [(464 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 120 = true ∨ valuation q 122 = true := by
  rw [value120, value121, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(464 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (474 : Vertex) [(464 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 111 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value111, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (466 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 121 = true ∨ valuation q 123 = true := by
  rw [value121, value122, value123, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(466 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (451 : Vertex) [(466 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 111 = true ∨ valuation q 123 = true := by
  rw [value111, value122, value123, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(451 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (466 : Vertex) [(451 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 44 = false ∨ valuation q 80 = false ∨ valuation q 114 = false := by
  rw [value44, value80, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (343 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 44 = false ∨ valuation q 80 = false ∨ valuation q 122 = false := by
  rw [value44, value80, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (343 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E050.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112050
