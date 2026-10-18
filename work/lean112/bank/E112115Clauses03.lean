import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 127 = true ∨ valuation q 7 = true ∨ valuation q 11 = true ∨ valuation q 21 = true := by
  rw [value7, value10, value11, value21, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(9 : Vertex), (15 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (12 : Vertex) [(9 : Vertex), (15 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 127 = true ∨ valuation q 7 = true ∨ valuation q 9 = true ∨ valuation q 21 = true := by
  rw [value7, value9, value10, value21, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(9 : Vertex), (12 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (15 : Vertex) [(9 : Vertex), (12 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 23 = false := by
  rw [value5, value8, value11, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (7 : Vertex) (11 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 23 = false := by
  rw [value5, value10, value11, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (7 : Vertex) (13 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 23 = false := by
  rw [value8, value10, value11, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (11 : Vertex) (13 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 23 = true := by
  rw [value8, value10, value11, value23, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(11 : Vertex), (13 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (7 : Vertex) [(11 : Vertex), (13 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 5 = true ∨ valuation q 10 = true ∨ valuation q 23 = true := by
  rw [value5, value10, value11, value23, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(7 : Vertex), (13 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (11 : Vertex) [(7 : Vertex), (13 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 23 = true := by
  rw [value5, value8, value11, value23, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(7 : Vertex), (11 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (13 : Vertex) [(7 : Vertex), (11 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 10 = true := by
  rw [value5, value8, value10, value11, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(7 : Vertex), (11 : Vertex), (13 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (31 : Vertex) [(7 : Vertex), (11 : Vertex), (13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value1, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 16 = false := by
  rw [value1, value12, value13, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (20 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 18 = false := by
  rw [value1, value12, value13, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value1, value12, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (18 : Vertex) (20 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 18 = false := by
  rw [value1, value12, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (18 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value1, value12, value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (20 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value12, value13, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (20 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 18 = false := by
  rw [value12, value13, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value12, value13, value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (20 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value12, value14, value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (18 : Vertex) (20 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value2, value12, value13, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (16 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 12 = true ∨ valuation q 15 = true := by
  rw [value12, value13, value15, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(16 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (1 : Vertex) [(16 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 15 = true := by
  rw [value2, value13, value15, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(1 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (16 : Vertex) [(1 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 12 = true := by
  rw [value2, value12, value13, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(1 : Vertex), (16 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (19 : Vertex) [(1 : Vertex), (16 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 3 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value3, value14, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 3 = false ∨ valuation q 17 = false ∨ valuation q 83 = false := by
  rw [value3, value14, value17, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (22 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 3 = false ∨ valuation q 31 = false ∨ valuation q 47 = false := by
  rw [value3, value14, value31, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (82 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value12, value14, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (16 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 47 = false := by
  rw [value12, value14, value31, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (16 : Vertex) (82 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 31 = false ∨ valuation q 47 = false := by
  rw [value14, value17, value31, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (22 : Vertex) (82 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 31 = false ∨ valuation q 47 = false ∨ valuation q 83 = false := by
  rw [value14, value31, value47, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (82 : Vertex) (146 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value4, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (3 : Vertex) (17 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 19 = false := by
  rw [value4, value13, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (3 : Vertex) (17 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E115.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112115
