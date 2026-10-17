import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 31 = false ∨ valuation q 66 = false ∨ valuation q 106 = false := by
  rw [value31, value66, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (287 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 31 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value31, value101, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 31 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value31, value101, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 31 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value31, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 31 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value31, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (411 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 31 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value31, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value66, value101, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value66, value101, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value66, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (411 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 66 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value66, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value101, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value101, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (411 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value101, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value104, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (411 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 234 = true ∨ valuation q 66 = true ∨ valuation q 101 = true ∨ valuation q 104 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value66, value101, value104, value105, value106, value107, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(287 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (159 : Vertex) [(287 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 234 = true ∨ valuation q 31 = true ∨ valuation q 101 = true ∨ valuation q 104 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value31, value101, value104, value105, value106, value107, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(159 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (287 : Vertex) [(159 : Vertex), (407 : Vertex), (411 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 32 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value32, value108, value109, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 85 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value85, value108, value109, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (449 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 85 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value85, value108, value111, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (452 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 85 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 119 = true := by
  rw [value85, value108, value109, value111, value119, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(384 : Vertex), (449 : Vertex), (452 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (192 : Vertex) [(384 : Vertex), (449 : Vertex), (452 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 32 = true ∨ valuation q 85 = true ∨ valuation q 109 = true ∨ valuation q 111 = true := by
  rw [value32, value85, value108, value109, value111, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(192 : Vertex), (384 : Vertex), (449 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (464 : Vertex) [(192 : Vertex), (384 : Vertex), (449 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value108, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value108, value109, value110, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 108 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value108, value109, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (448 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value109, value110, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 108 = false ∨ valuation q 114 = false := by
  rw [value108, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (449 : Vertex) (448 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide)

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value110, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (449 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide)

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 236 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value108, value109, value110, value112, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(448 : Vertex), (451 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (457 : Vertex) [(448 : Vertex), (451 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value109, value110, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (455 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value109, value110, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 115 = false ∨ valuation q 121 = false := by
  rw [value109, value110, value115, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 121 = false := by
  rw [value110, value113, value115, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (455 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E052.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112052
