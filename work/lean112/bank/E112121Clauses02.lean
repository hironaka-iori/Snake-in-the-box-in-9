import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 20 = false := by
  rw [value8, value9, value12, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (32 : Vertex) (37 : Vertex) (49 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value8, value9, value16, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (32 : Vertex) (41 : Vertex) (49 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 135 = true ∨ valuation q 8 = true ∨ valuation q 12 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 45 = true ∨ valuation q 70 = true := by
  rw [value8, value9, value12, value16, value20, value45, value70, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(32 : Vertex), (37 : Vertex), (41 : Vertex), (49 : Vertex), (161 : Vertex), (289 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (1 : Vertex) [(32 : Vertex), (37 : Vertex), (41 : Vertex), (49 : Vertex), (161 : Vertex), (289 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value8, value10, value13, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (32 : Vertex) (38 : Vertex) (50 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value8, value10, value17, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (32 : Vertex) (42 : Vertex) (50 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 136 = true ∨ valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 21 = true := by
  rw [value10, value13, value17, value21, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (32 : Vertex) → w ∈ [(38 : Vertex), (42 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (32 : Vertex) [(38 : Vertex), (42 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 136 = true ∨ valuation q 8 = true ∨ valuation q 17 = true ∨ valuation q 21 = true := by
  rw [value8, value10, value17, value21, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(32 : Vertex), (42 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (38 : Vertex) [(32 : Vertex), (42 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 136 = true ∨ valuation q 8 = true ∨ valuation q 13 = true ∨ valuation q 21 = true := by
  rw [value8, value10, value13, value21, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(32 : Vertex), (38 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (42 : Vertex) [(32 : Vertex), (38 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 136 = true ∨ valuation q 8 = true ∨ valuation q 13 = true ∨ valuation q 17 = true := by
  rw [value8, value10, value13, value17, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(32 : Vertex), (38 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (50 : Vertex) [(32 : Vertex), (38 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value8, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (32 : Vertex) (37 : Vertex) (38 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 18 = false := by
  rw [value8, value11, value12, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (32 : Vertex) (37 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 23 = false := by
  rw [value8, value11, value13, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (32 : Vertex) (38 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 18 = false ∨ valuation q 23 = false := by
  rw [value8, value11, value18, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (32 : Vertex) (44 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 23 = false := by
  rw [value11, value12, value13, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (37 : Vertex) (38 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 137 = true ∨ valuation q 8 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 23 = true := by
  rw [value8, value11, value12, value13, value23, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (44 : Vertex) → w ∈ [(32 : Vertex), (37 : Vertex), (38 : Vertex), (52 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (44 : Vertex) [(32 : Vertex), (37 : Vertex), (38 : Vertex), (52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 137 = true ∨ valuation q 8 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 18 = true := by
  rw [value8, value11, value12, value13, value18, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (52 : Vertex) → w ∈ [(32 : Vertex), (37 : Vertex), (38 : Vertex), (44 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (52 : Vertex) [(32 : Vertex), (37 : Vertex), (38 : Vertex), (44 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 14 = false := by
  rw [value9, value11, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (33 : Vertex) (36 : Vertex) (39 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 24 = false := by
  rw [value9, value11, value12, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (33 : Vertex) (36 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 46 = false := by
  rw [value9, value11, value12, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (33 : Vertex) (36 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 24 = false := by
  rw [value9, value12, value14, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (33 : Vertex) (39 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 46 = false := by
  rw [value9, value12, value14, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (33 : Vertex) (39 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 24 = false ∨ valuation q 46 = false := by
  rw [value9, value12, value24, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (33 : Vertex) (53 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 24 = false := by
  rw [value11, value12, value14, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (36 : Vertex) (39 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 46 = false := by
  rw [value11, value12, value14, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (36 : Vertex) (39 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 24 = false ∨ valuation q 46 = false := by
  rw [value11, value12, value24, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (36 : Vertex) (53 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 24 = false ∨ valuation q 46 = false := by
  rw [value12, value14, value24, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (37 : Vertex) (39 : Vertex) (53 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 138 = true ∨ valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 46 = true := by
  rw [value9, value11, value12, value14, value46, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(33 : Vertex), (36 : Vertex), (39 : Vertex), (165 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (53 : Vertex) [(33 : Vertex), (36 : Vertex), (39 : Vertex), (165 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 138 = true ∨ valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 24 = true := by
  rw [value9, value11, value12, value14, value24, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(33 : Vertex), (36 : Vertex), (39 : Vertex), (53 : Vertex)] := by decide
  have hg := other_cover q (37 : Vertex) (165 : Vertex) [(33 : Vertex), (36 : Vertex), (39 : Vertex), (53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value3, value10, value11, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (34 : Vertex) (36 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 14 = false := by
  rw [value3, value10, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (34 : Vertex) (39 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 19 = false := by
  rw [value3, value10, value13, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (34 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 25 = false := by
  rw [value3, value10, value13, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (34 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E121.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112121
