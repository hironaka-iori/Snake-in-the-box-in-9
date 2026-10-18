import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 75 = false := by
  rw [value1, value5, value7, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (45 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 22 = false ∨ valuation q 75 = false := by
  rw [value5, value7, value22, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (45 : Vertex) (105 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 129 = true ∨ valuation q 7 = true ∨ valuation q 22 = true ∨ valuation q 75 = true := by
  rw [value5, value7, value22, value75, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(45 : Vertex), (105 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (33 : Vertex) [(45 : Vertex), (105 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 129 = true ∨ valuation q 1 = true ∨ valuation q 22 = true ∨ valuation q 75 = true := by
  rw [value1, value5, value22, value75, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (45 : Vertex) → w ∈ [(33 : Vertex), (105 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (45 : Vertex) [(33 : Vertex), (105 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 129 = true ∨ valuation q 1 = true ∨ valuation q 7 = true ∨ valuation q 75 = true := by
  rw [value1, value5, value7, value75, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(33 : Vertex), (45 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (105 : Vertex) [(33 : Vertex), (45 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 129 = true ∨ valuation q 1 = true ∨ valuation q 7 = true ∨ valuation q 22 = true := by
  rw [value1, value5, value7, value22, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(33 : Vertex), (45 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (297 : Vertex) [(33 : Vertex), (45 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 2 = false ∨ valuation q 15 = false ∨ valuation q 39 = false := by
  rw [value2, value6, value15, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (58 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 39 = false := by
  rw [value6, value15, value23, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (58 : Vertex) (106 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 15 = true ∨ valuation q 23 = true ∨ valuation q 39 = true := by
  rw [value6, value15, value23, value39, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(58 : Vertex), (106 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (34 : Vertex) [(58 : Vertex), (106 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 23 = true ∨ valuation q 39 = true := by
  rw [value2, value6, value23, value39, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(34 : Vertex), (106 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (58 : Vertex) [(34 : Vertex), (106 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 15 = true ∨ valuation q 39 = true := by
  rw [value2, value6, value15, value39, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(34 : Vertex), (58 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (106 : Vertex) [(34 : Vertex), (58 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 15 = true ∨ valuation q 23 = true := by
  rw [value2, value6, value15, value23, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(34 : Vertex), (58 : Vertex), (106 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (170 : Vertex) [(34 : Vertex), (58 : Vertex), (106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 131 = true ∨ valuation q 8 = true := by
  rw [value7, value8, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (45 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(47 : Vertex)] := by decide
  have hg := other_cover q (45 : Vertex) (41 : Vertex) [(47 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 131 = true ∨ valuation q 5 = true := by
  rw [value5, value7, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (45 : Vertex) w → w ∈ region → w ≠ (47 : Vertex) → w ∈ [(41 : Vertex)] := by decide
  have hg := other_cover q (45 : Vertex) (47 : Vertex) [(41 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 18 = false := by
  rw [value4, value7, value8, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (47 : Vertex) (39 : Vertex) (45 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 7 = true ∨ valuation q 18 = true := by
  rw [value7, value8, value18, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (47 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(45 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (47 : Vertex) (39 : Vertex) [(45 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 4 = true ∨ valuation q 18 = true := by
  rw [value4, value8, value18, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (47 : Vertex) w → w ∈ region → w ≠ (45 : Vertex) → w ∈ [(39 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (47 : Vertex) (45 : Vertex) [(39 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 4 = true ∨ valuation q 7 = true := by
  rw [value4, value7, value8, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (47 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(39 : Vertex), (45 : Vertex)] := by decide
  have hg := other_cover q (47 : Vertex) (63 : Vertex) [(39 : Vertex), (45 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value9, value10, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (48 : Vertex) (49 : Vertex) (52 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 133 = true ∨ valuation q 10 = true ∨ valuation q 14 = true := by
  rw [value9, value10, value14, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (52 : Vertex) → w ∈ [(49 : Vertex), (56 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (52 : Vertex) [(49 : Vertex), (56 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 11 = false := by
  rw [value1, value9, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (48 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 9 = true ∨ valuation q 11 = true := by
  rw [value9, value10, value11, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(48 : Vertex), (51 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (33 : Vertex) [(48 : Vertex), (51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 1 = true ∨ valuation q 11 = true := by
  rw [value1, value10, value11, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(33 : Vertex), (51 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (48 : Vertex) [(33 : Vertex), (51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 1 = true ∨ valuation q 9 = true := by
  rw [value1, value9, value10, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (51 : Vertex) → w ∈ [(33 : Vertex), (48 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (51 : Vertex) [(33 : Vertex), (48 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 13 = false := by
  rw [value3, value10, value11, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (35 : Vertex) (49 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 135 = true ∨ valuation q 10 = true ∨ valuation q 13 = true := by
  rw [value10, value11, value13, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (51 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(49 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (51 : Vertex) (35 : Vertex) [(49 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 135 = true ∨ valuation q 3 = true ∨ valuation q 13 = true := by
  rw [value3, value11, value13, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (51 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(35 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (51 : Vertex) (49 : Vertex) [(35 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 16 = false ∨ valuation q 79 = false := by
  rw [value9, value12, value16, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (52 : Vertex) (48 : Vertex) (60 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 16 = true ∨ valuation q 79 = true := by
  rw [value12, value16, value79, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(60 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (48 : Vertex) [(60 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 9 = true ∨ valuation q 79 = true := by
  rw [value9, value12, value79, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (60 : Vertex) → w ∈ [(48 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (60 : Vertex) [(48 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 9 = true ∨ valuation q 16 = true := by
  rw [value9, value12, value16, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(48 : Vertex), (60 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (308 : Vertex) [(48 : Vertex), (60 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 27 = false := by
  rw [value4, value11, value13, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (51 : Vertex) (119 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E008.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112008
