import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 121 = true ∨ valuation q 8 = true := by
  rw [value1, value8, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (9 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(41 : Vertex)] := by decide
  have hg := other_cover q (9 : Vertex) (25 : Vertex) [(41 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 121 = true ∨ valuation q 4 = true := by
  rw [value1, value4, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (9 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(25 : Vertex)] := by decide
  have hg := other_cover q (9 : Vertex) (41 : Vertex) [(25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 122 = true ∨ valuation q 3 = true := by
  rw [value2, value3, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(19 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (25 : Vertex) [(19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 123 = true := by
  rw [value3, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (19 : Vertex) (17 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 124 = true ∨ valuation q 2 = true := by
  rw [value2, value4, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(17 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (9 : Vertex) [(17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 124 = true ∨ valuation q 1 = true := by
  rw [value1, value4, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(9 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (17 : Vertex) [(9 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 125 = true ∨ valuation q 8 = true := by
  rw [value5, value8, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(41 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (35 : Vertex) [(41 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 7 = true := by
  rw [value6, value7, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(39 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (33 : Vertex) [(39 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 5 = true := by
  rw [value5, value6, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(33 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (39 : Vertex) [(33 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 29 = false := by
  rw [value6, value7, value13, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (35 : Vertex) (103 : Vertex) (167 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 127 = true ∨ valuation q 13 = true ∨ valuation q 29 = true := by
  rw [value7, value13, value29, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(103 : Vertex), (167 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (35 : Vertex) [(103 : Vertex), (167 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 15 = false := by
  rw [value1, value5, value8, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (33 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 31 = false := by
  rw [value1, value5, value8, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (33 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 31 = false := by
  rw [value1, value8, value15, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (105 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 130 = true ∨ valuation q 14 = true := by
  rw [value10, value14, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (98 : Vertex) → w ∈ [(104 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (98 : Vertex) [(104 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 131 = true ∨ valuation q 10 = true ∨ valuation q 19 = true := by
  rw [value10, value11, value19, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (102 : Vertex) → w ∈ [(96 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (102 : Vertex) [(96 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 131 = true ∨ valuation q 10 = true ∨ valuation q 12 = true := by
  rw [value10, value11, value12, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(96 : Vertex), (102 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (114 : Vertex) [(96 : Vertex), (102 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 16 = false := by
  rw [value11, value12, value13, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (103 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 64 = false := by
  rw [value11, value12, value13, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (103 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 16 = false ∨ valuation q 47 = false := by
  rw [value11, value12, value16, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (110 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 16 = false ∨ valuation q 64 = false := by
  rw [value11, value12, value16, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (110 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 47 = false := by
  rw [value12, value13, value16, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (103 : Vertex) (110 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 64 = false := by
  rw [value12, value13, value16, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (103 : Vertex) (110 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 133 = true ∨ valuation q 7 = true ∨ valuation q 12 = true := by
  rw [value7, value12, value13, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(39 : Vertex), (102 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (111 : Vertex) [(39 : Vertex), (102 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 134 = true ∨ valuation q 15 = true := by
  rw [value14, value15, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(105 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (96 : Vertex) [(105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 14 = false ∨ valuation q 22 = false := by
  rw [value8, value14, value15, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (104 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 14 = false ∨ valuation q 65 = false := by
  rw [value8, value14, value15, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (104 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 65 = false := by
  rw [value14, value15, value22, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (104 : Vertex) (121 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value18, value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (115 : Vertex) (117 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 138 = true ∨ valuation q 21 = true ∨ valuation q 22 = true := by
  rw [value18, value21, value22, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(117 : Vertex), (121 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (115 : Vertex) [(117 : Vertex), (121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 139 = true ∨ valuation q 20 = true := by
  rw [value19, value20, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (114 : Vertex) w → w ∈ region → w ≠ (98 : Vertex) → w ∈ [(115 : Vertex)] := by decide
  have hg := other_cover q (114 : Vertex) (98 : Vertex) [(115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 140 = true ∨ valuation q 18 = true := by
  rw [value18, value20, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(113 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (114 : Vertex) [(113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E152.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112152
