import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 10 = false := by
  rw [value1, value3, value5, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (35 : Vertex) (41 : Vertex) (49 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 33 = false := by
  rw [value1, value3, value5, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (35 : Vertex) (41 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 71 = false := by
  rw [value1, value3, value5, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (35 : Vertex) (41 : Vertex) (289 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 33 = false := by
  rw [value1, value3, value10, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (35 : Vertex) (49 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 71 = false := by
  rw [value1, value3, value10, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (35 : Vertex) (49 : Vertex) (289 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 71 = false := by
  rw [value1, value3, value33, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (35 : Vertex) (161 : Vertex) (289 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 33 = false := by
  rw [value1, value5, value10, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (41 : Vertex) (49 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 71 = false := by
  rw [value1, value5, value10, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (41 : Vertex) (49 : Vertex) (289 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 33 = false ∨ valuation q 71 = false := by
  rw [value1, value5, value33, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (41 : Vertex) (161 : Vertex) (289 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 33 = false ∨ valuation q 71 = false := by
  rw [value1, value10, value33, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (49 : Vertex) (161 : Vertex) (289 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 125 = true ∨ valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 33 = true ∨ valuation q 71 = true := by
  rw [value1, value3, value5, value33, value71, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(35 : Vertex), (41 : Vertex), (161 : Vertex), (289 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (49 : Vertex) [(35 : Vertex), (41 : Vertex), (161 : Vertex), (289 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 19 = false := by
  rw [value2, value3, value6, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (35 : Vertex) (42 : Vertex) (98 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 34 = false := by
  rw [value2, value3, value6, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (35 : Vertex) (42 : Vertex) (162 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 19 = false ∨ valuation q 34 = false := by
  rw [value2, value3, value19, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (35 : Vertex) (98 : Vertex) (162 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 34 = false := by
  rw [value2, value6, value19, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (34 : Vertex) (42 : Vertex) (98 : Vertex) (162 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 126 = true ∨ valuation q 6 = true ∨ valuation q 19 = true ∨ valuation q 34 = true := by
  rw [value2, value6, value19, value34, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(42 : Vertex), (98 : Vertex), (162 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (35 : Vertex) [(42 : Vertex), (98 : Vertex), (162 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 126 = true ∨ valuation q 3 = true ∨ valuation q 19 = true ∨ valuation q 34 = true := by
  rw [value2, value3, value19, value34, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(35 : Vertex), (98 : Vertex), (162 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (42 : Vertex) [(35 : Vertex), (98 : Vertex), (162 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 126 = true ∨ valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 34 = true := by
  rw [value2, value3, value6, value34, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (34 : Vertex) w → w ∈ region → w ≠ (98 : Vertex) → w ∈ [(35 : Vertex), (42 : Vertex), (162 : Vertex)] := by decide
  have hg := other_cover q (34 : Vertex) (98 : Vertex) [(35 : Vertex), (42 : Vertex), (162 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 11 = false := by
  rw [value2, value3, value4, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (35 : Vertex) (34 : Vertex) (39 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 127 = true ∨ valuation q 2 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value2, value3, value4, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(34 : Vertex), (39 : Vertex), (51 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (33 : Vertex) [(34 : Vertex), (39 : Vertex), (51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 127 = true ∨ valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value1, value3, value4, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(33 : Vertex), (39 : Vertex), (51 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (34 : Vertex) [(33 : Vertex), (39 : Vertex), (51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 127 = true ∨ valuation q 1 = true ∨ valuation q 2 = true ∨ valuation q 11 = true := by
  rw [value1, value2, value3, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(33 : Vertex), (34 : Vertex), (51 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (39 : Vertex) [(33 : Vertex), (34 : Vertex), (51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 127 = true ∨ valuation q 1 = true ∨ valuation q 2 = true ∨ valuation q 4 = true := by
  rw [value1, value2, value3, value4, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (51 : Vertex) → w ∈ [(33 : Vertex), (34 : Vertex), (39 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (51 : Vertex) [(33 : Vertex), (34 : Vertex), (39 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 13 = false := by
  rw [value3, value4, value8, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (35 : Vertex) (47 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 20 = false := by
  rw [value3, value4, value8, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (35 : Vertex) (47 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 73 = false := by
  rw [value3, value4, value8, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (35 : Vertex) (47 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 73 = false := by
  rw [value3, value4, value13, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (35 : Vertex) (55 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 20 = false ∨ valuation q 73 = false := by
  rw [value3, value4, value20, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (35 : Vertex) (103 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 13 = false ∨ valuation q 73 = false := by
  rw [value4, value8, value13, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (47 : Vertex) (55 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 20 = false ∨ valuation q 73 = false := by
  rw [value4, value8, value20, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (47 : Vertex) (103 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 128 = true ∨ valuation q 3 = true ∨ valuation q 13 = true ∨ valuation q 20 = true ∨ valuation q 73 = true := by
  rw [value3, value4, value13, value20, value73, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (47 : Vertex) → w ∈ [(35 : Vertex), (55 : Vertex), (103 : Vertex), (295 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (47 : Vertex) [(35 : Vertex), (55 : Vertex), (103 : Vertex), (295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 22 = false := by
  rw [value1, value5, value7, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (45 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E008.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112008
