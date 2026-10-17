import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 124 = true := by
  rw [value1, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (8 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true ∨ valuation q 3 = true ∨ valuation q 7 = true := by
  rw [value1, value2, value3, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (12 : Vertex), (40 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (8 : Vertex) [(0 : Vertex), (12 : Vertex), (40 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 125 = true ∨ valuation q 1 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(0 : Vertex), (12 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (40 : Vertex) [(0 : Vertex), (12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 126 = true := by
  rw [value3, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (12 : Vertex) (8 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 127 = true := by
  rw [value4, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (33 : Vertex) (35 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 128 = true ∨ valuation q 4 = true ∨ valuation q 10 = true := by
  rw [value4, value5, value10, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(33 : Vertex), (51 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (39 : Vertex) [(33 : Vertex), (51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 128 = true ∨ valuation q 4 = true ∨ valuation q 6 = true := by
  rw [value4, value5, value6, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (51 : Vertex) → w ∈ [(33 : Vertex), (39 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (51 : Vertex) [(33 : Vertex), (39 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 16 = false ∨ valuation q 51 = false := by
  rw [value5, value6, value16, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (35 : Vertex) (167 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 129 = true ∨ valuation q 16 = true ∨ valuation q 51 = true := by
  rw [value6, value16, value51, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(167 : Vertex), (295 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (35 : Vertex) [(167 : Vertex), (295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 129 = true ∨ valuation q 5 = true ∨ valuation q 51 = true := by
  rw [value5, value6, value51, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(35 : Vertex), (295 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (167 : Vertex) [(35 : Vertex), (295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 129 = true ∨ valuation q 5 = true ∨ valuation q 16 = true := by
  rw [value5, value6, value16, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(35 : Vertex), (167 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (295 : Vertex) [(35 : Vertex), (167 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 17 = false ∨ valuation q 52 = false := by
  rw [value2, value7, value17, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (8 : Vertex) (168 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 130 = true ∨ valuation q 12 = true ∨ valuation q 17 = true ∨ valuation q 52 = true := by
  rw [value7, value12, value17, value52, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(56 : Vertex), (168 : Vertex), (296 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (8 : Vertex) [(56 : Vertex), (168 : Vertex), (296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 17 = true ∨ valuation q 52 = true := by
  rw [value2, value7, value17, value52, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (56 : Vertex) → w ∈ [(8 : Vertex), (168 : Vertex), (296 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (56 : Vertex) [(8 : Vertex), (168 : Vertex), (296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 12 = true ∨ valuation q 17 = true := by
  rw [value2, value7, value12, value17, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(8 : Vertex), (56 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (296 : Vertex) [(8 : Vertex), (56 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value8, value9, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (48 : Vertex) (50 : Vertex) (52 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 131 = true ∨ valuation q 11 = true ∨ valuation q 12 = true := by
  rw [value8, value11, value12, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(52 : Vertex), (56 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (50 : Vertex) [(52 : Vertex), (56 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 131 = true ∨ valuation q 9 = true ∨ valuation q 12 = true := by
  rw [value8, value9, value12, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (52 : Vertex) → w ∈ [(50 : Vertex), (56 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (52 : Vertex) [(50 : Vertex), (56 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 131 = true ∨ valuation q 9 = true ∨ valuation q 11 = true := by
  rw [value8, value9, value11, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (56 : Vertex) → w ∈ [(50 : Vertex), (52 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (56 : Vertex) [(50 : Vertex), (52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 8 = false ∨ valuation q 10 = false := by
  rw [value8, value10, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (50 : Vertex) (48 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 132 = true ∨ valuation q 10 = true := by
  rw [value9, value10, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(51 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (48 : Vertex) [(51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 132 = true ∨ valuation q 8 = true := by
  rw [value8, value9, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (51 : Vertex) → w ∈ [(48 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (51 : Vertex) [(48 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 58 = false := by
  rw [value5, value9, value10, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (35 : Vertex) (50 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 133 = true ∨ valuation q 9 = true ∨ valuation q 58 = true := by
  rw [value9, value10, value58, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (51 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(50 : Vertex), (307 : Vertex)] := by decide
  have hg := other_cover q (51 : Vertex) (35 : Vertex) [(50 : Vertex), (307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 133 = true ∨ valuation q 5 = true ∨ valuation q 58 = true := by
  rw [value5, value10, value58, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (51 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(35 : Vertex), (307 : Vertex)] := by decide
  have hg := other_cover q (51 : Vertex) (50 : Vertex) [(35 : Vertex), (307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 22 = false ∨ valuation q 59 = false := by
  rw [value8, value11, value22, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (52 : Vertex) (48 : Vertex) (180 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 134 = true ∨ valuation q 22 = true ∨ valuation q 59 = true := by
  rw [value11, value22, value59, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(180 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (48 : Vertex) [(180 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 135 = true ∨ valuation q 7 = true := by
  rw [value7, value12, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(40 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (48 : Vertex) [(40 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 136 = true ∨ valuation q 15 = true ∨ valuation q 17 = true := by
  rw [value13, value15, value17, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(164 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (162 : Vertex) [(164 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 136 = true ∨ valuation q 14 = true ∨ valuation q 17 = true := by
  rw [value13, value14, value17, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(162 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (164 : Vertex) [(162 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = true ∨ valuation q 18 = true := by
  rw [value13, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ∈ [(160 : Vertex), (170 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (162 : Vertex) [(160 : Vertex), (170 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 137 = true ∨ valuation q 18 = true := by
  rw [value14, value18, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(170 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (160 : Vertex) [(170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E097.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112097
