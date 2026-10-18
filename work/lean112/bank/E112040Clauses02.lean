import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 132 = true ∨ valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 14 = true := by
  rw [value11, value12, value13, value14, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(48 : Vertex), (51 : Vertex), (53 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (57 : Vertex) [(48 : Vertex), (51 : Vertex), (53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 32 = false := by
  rw [value12, value13, value15, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (49 : Vertex) (55 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 32 = false ∨ valuation q 52 = false := by
  rw [value12, value13, value32, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (49 : Vertex) (115 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value3, value12, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (37 : Vertex) (49 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 134 = true ∨ valuation q 12 = true ∨ valuation q 15 = true := by
  rw [value12, value14, value15, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(49 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (37 : Vertex) [(49 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 19 = false := by
  rw [value13, value14, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (53 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 35 = false := by
  rw [value13, value15, value19, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (63 : Vertex) (119 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 35 = false := by
  rw [value14, value15, value19, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (53 : Vertex) (63 : Vertex) (119 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 135 = true ∨ valuation q 13 = true ∨ valuation q 19 = true ∨ valuation q 35 = true := by
  rw [value13, value15, value19, value35, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(51 : Vertex), (63 : Vertex), (119 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (53 : Vertex) [(51 : Vertex), (63 : Vertex), (119 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 135 = true ∨ valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 35 = true := by
  rw [value13, value14, value15, value35, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(51 : Vertex), (53 : Vertex), (119 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (63 : Vertex) [(51 : Vertex), (53 : Vertex), (119 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 5 = false ∨ valuation q 36 = false ∨ valuation q 55 = false := by
  rw [value5, value16, value36, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (56 : Vertex) (40 : Vertex) (120 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 36 = false ∨ valuation q 55 = false := by
  rw [value16, value17, value36, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (56 : Vertex) (57 : Vertex) (120 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 136 = true ∨ valuation q 11 = true ∨ valuation q 17 = true ∨ valuation q 36 = true ∨ valuation q 55 = true := by
  rw [value11, value16, value17, value36, value55, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(48 : Vertex), (57 : Vertex), (120 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (40 : Vertex) [(48 : Vertex), (57 : Vertex), (120 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 136 = true ∨ valuation q 5 = true ∨ valuation q 17 = true ∨ valuation q 36 = true ∨ valuation q 55 = true := by
  rw [value5, value16, value17, value36, value55, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(40 : Vertex), (57 : Vertex), (120 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (48 : Vertex) [(40 : Vertex), (57 : Vertex), (120 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 136 = true ∨ valuation q 5 = true ∨ valuation q 11 = true ∨ valuation q 36 = true ∨ valuation q 55 = true := by
  rw [value5, value11, value16, value36, value55, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(40 : Vertex), (48 : Vertex), (120 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (57 : Vertex) [(40 : Vertex), (48 : Vertex), (120 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 136 = true ∨ valuation q 5 = true ∨ valuation q 11 = true ∨ valuation q 17 = true ∨ valuation q 55 = true := by
  rw [value5, value11, value16, value17, value55, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(40 : Vertex), (48 : Vertex), (57 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (120 : Vertex) [(40 : Vertex), (48 : Vertex), (57 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 136 = true ∨ valuation q 5 = true ∨ valuation q 11 = true ∨ valuation q 17 = true ∨ valuation q 36 = true := by
  rw [value5, value11, value16, value17, value36, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(40 : Vertex), (48 : Vertex), (57 : Vertex), (120 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (184 : Vertex) [(40 : Vertex), (48 : Vertex), (57 : Vertex), (120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 16 = false := by
  rw [value6, value12, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (49 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 37 = false := by
  rw [value6, value12, value17, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (49 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 6 = false ∨ valuation q 16 = false ∨ valuation q 37 = false := by
  rw [value6, value16, value17, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (56 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 37 = false := by
  rw [value12, value16, value17, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (49 : Vertex) (56 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 137 = true ∨ valuation q 12 = true ∨ valuation q 16 = true ∨ valuation q 37 = true := by
  rw [value12, value16, value17, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(49 : Vertex), (56 : Vertex), (121 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (41 : Vertex) [(49 : Vertex), (56 : Vertex), (121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 137 = true ∨ valuation q 6 = true ∨ valuation q 12 = true ∨ valuation q 37 = true := by
  rw [value6, value12, value17, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (56 : Vertex) → w ∈ [(41 : Vertex), (49 : Vertex), (121 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (56 : Vertex) [(41 : Vertex), (49 : Vertex), (121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 138 = true ∨ valuation q 19 = true ∨ valuation q 41 = true := by
  rw [value18, value19, value41, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(63 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (46 : Vertex) [(63 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 138 = true ∨ valuation q 10 = true ∨ valuation q 41 = true := by
  rw [value10, value18, value41, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(46 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (63 : Vertex) [(46 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 138 = true ∨ valuation q 10 = true ∨ valuation q 19 = true := by
  rw [value10, value18, value19, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(46 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (126 : Vertex) [(46 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 42 = false := by
  rw [value15, value18, value19, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (55 : Vertex) (62 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 139 = true ∨ valuation q 18 = true ∨ valuation q 42 = true := by
  rw [value18, value19, value42, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(62 : Vertex), (127 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (55 : Vertex) [(62 : Vertex), (127 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 139 = true ∨ valuation q 15 = true ∨ valuation q 42 = true := by
  rw [value15, value19, value42, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(55 : Vertex), (127 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (62 : Vertex) [(55 : Vertex), (127 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value20, value21, value22, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (97 : Vertex) (98 : Vertex) (112 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 92 = false := by
  rw [value20, value21, value30, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (97 : Vertex) (112 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 92 = false := by
  rw [value20, value22, value30, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (98 : Vertex) (112 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E040.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112040
