import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 96 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 127 = true := by
  rw [value96, value117, value119, value120, value127, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(359 : Vertex), (483 : Vertex), (485 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(359 : Vertex), (483 : Vertex), (485 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 96 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 126 = true := by
  rw [value96, value117, value119, value120, value126, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(359 : Vertex), (483 : Vertex), (485 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (503 : Vertex) [(359 : Vertex), (483 : Vertex), (485 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 60 = false ∨ valuation q 108 = false ∨ valuation q 122 = false := by
  rw [value60, value108, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (456 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 60 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value60, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (232 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 108 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value108, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (456 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 108 = true ∨ valuation q 122 = true ∨ valuation q 124 = true := by
  rw [value108, value121, value122, value124, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(456 : Vertex), (490 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (232 : Vertex) [(456 : Vertex), (490 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 60 = true ∨ valuation q 122 = true ∨ valuation q 124 = true := by
  rw [value60, value121, value122, value124, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(232 : Vertex), (490 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (456 : Vertex) [(232 : Vertex), (490 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 97 = true ∨ valuation q 116 = true ∨ valuation q 121 = true ∨ valuation q 123 = true := by
  rw [value97, value116, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ∈ [(362 : Vertex), (482 : Vertex), (488 : Vertex), (491 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (490 : Vertex) [(362 : Vertex), (482 : Vertex), (488 : Vertex), (491 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 116 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value116, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (482 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 97 = true ∨ valuation q 121 = true ∨ valuation q 123 = true := by
  rw [value97, value121, value122, value123, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(362 : Vertex), (488 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (482 : Vertex) [(362 : Vertex), (488 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 97 = true ∨ valuation q 116 = true ∨ valuation q 123 = true := by
  rw [value97, value116, value122, value123, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(362 : Vertex), (482 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (488 : Vertex) [(362 : Vertex), (482 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 97 = true ∨ valuation q 116 = true ∨ valuation q 121 = true := by
  rw [value97, value116, value121, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(362 : Vertex), (482 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (491 : Vertex) [(362 : Vertex), (482 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 62 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value62, value110, value117, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (459 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 62 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value62, value110, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (459 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 62 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value62, value122, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (235 : Vertex) (490 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 110 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value110, value117, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (459 : Vertex) (483 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 110 = false ∨ valuation q 117 = false ∨ valuation q 126 = false := by
  rw [value110, value117, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (459 : Vertex) (483 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 110 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value110, value122, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (459 : Vertex) (490 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 117 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value117, value122, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (483 : Vertex) (490 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 118 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value118, value121, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (484 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 251 = true ∨ valuation q 118 = true ∨ valuation q 121 = true ∨ valuation q 125 = true := by
  rw [value118, value121, value124, value125, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(484 : Vertex), (488 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (236 : Vertex) [(484 : Vertex), (488 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 251 = true ∨ valuation q 63 = true ∨ valuation q 121 = true ∨ valuation q 125 = true := by
  rw [value63, value121, value124, value125, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (484 : Vertex) → w ∈ [(236 : Vertex), (488 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (484 : Vertex) [(236 : Vertex), (488 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 251 = true ∨ valuation q 63 = true ∨ valuation q 118 = true ∨ valuation q 125 = true := by
  rw [value63, value118, value124, value125, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(236 : Vertex), (484 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (488 : Vertex) [(236 : Vertex), (484 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 64 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value64, value111, value119, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (461 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 64 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value64, value124, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (492 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 98 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value98, value111, value119, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (461 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 98 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value98, value111, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (461 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 98 = false ∨ valuation q 111 = false ∨ valuation q 126 = false := by
  rw [value98, value111, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (461 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 98 = false ∨ valuation q 119 = false ∨ valuation q 124 = false := by
  rw [value98, value119, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (485 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 98 = false ∨ valuation q 119 = false ∨ valuation q 126 = false := by
  rw [value98, value119, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (485 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 98 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value98, value124, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (492 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 111 = false ∨ valuation q 119 = false ∨ valuation q 124 = false := by
  rw [value111, value119, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (461 : Vertex) (485 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E260.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112260
