import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 127 = true ∨ valuation q 8 = true := by
  rw [value1, value8, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(32 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(32 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 127 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (32 : Vertex) → w ∈ [(1 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (32 : Vertex) [(1 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 1 = false ∨ valuation q 4 = false := by
  rw [value1, value4, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (1 : Vertex) (0 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 4 = false ∨ valuation q 9 = false := by
  rw [value4, value9, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (1 : Vertex) (17 : Vertex) (33 : Vertex) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 128 = true ∨ valuation q 4 = true ∨ valuation q 9 = true := by
  rw [value2, value4, value9, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(17 : Vertex), (33 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(17 : Vertex), (33 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 128 = true ∨ valuation q 1 = true ∨ valuation q 9 = true := by
  rw [value1, value2, value9, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex), (33 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex), (33 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 33 = false := by
  rw [value3, value7, value13, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (22 : Vertex) (38 : Vertex) (70 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 129 = true ∨ valuation q 13 = true ∨ valuation q 33 = true := by
  rw [value3, value13, value33, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(38 : Vertex), (70 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(38 : Vertex), (70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 129 = true ∨ valuation q 7 = true ∨ valuation q 33 = true := by
  rw [value3, value7, value33, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(22 : Vertex), (70 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (38 : Vertex) [(22 : Vertex), (70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 129 = true ∨ valuation q 7 = true ∨ valuation q 13 = true := by
  rw [value3, value7, value13, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(22 : Vertex), (38 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (70 : Vertex) [(22 : Vertex), (38 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 20 = false := by
  rw [value2, value4, value6, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (19 : Vertex) (49 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 130 = true ∨ valuation q 6 = true ∨ valuation q 20 = true := by
  rw [value4, value6, value20, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(19 : Vertex), (49 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (1 : Vertex) [(19 : Vertex), (49 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 20 = true := by
  rw [value2, value4, value20, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(1 : Vertex), (49 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (19 : Vertex) [(1 : Vertex), (49 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 6 = true := by
  rw [value2, value4, value6, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(1 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (49 : Vertex) [(1 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 21 = false := by
  rw [value5, value6, value7, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (19 : Vertex) (22 : Vertex) (50 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 131 = true ∨ valuation q 7 = true ∨ valuation q 21 = true := by
  rw [value5, value7, value21, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(22 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (19 : Vertex) [(22 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 131 = true ∨ valuation q 6 = true ∨ valuation q 21 = true := by
  rw [value5, value6, value21, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(19 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(19 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 131 = true ∨ valuation q 6 = true ∨ valuation q 7 = true := by
  rw [value5, value6, value7, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(19 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (50 : Vertex) [(19 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 22 = false := by
  rw [value4, value5, value6, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (17 : Vertex) (18 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 132 = true ∨ valuation q 5 = true ∨ valuation q 22 = true := by
  rw [value5, value6, value22, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(18 : Vertex), (51 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (17 : Vertex) [(18 : Vertex), (51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 132 = true ∨ valuation q 4 = true ∨ valuation q 22 = true := by
  rw [value4, value6, value22, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(17 : Vertex), (51 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (18 : Vertex) [(17 : Vertex), (51 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 132 = true ∨ valuation q 4 = true ∨ valuation q 5 = true := by
  rw [value4, value5, value6, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (51 : Vertex) → w ∈ [(17 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (51 : Vertex) [(17 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 25 = false := by
  rw [value3, value5, value7, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (6 : Vertex) (18 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 5 = false ∨ valuation q 25 = false := by
  rw [value5, value25, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (22 : Vertex) (18 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 133 = true ∨ valuation q 5 = true ∨ valuation q 25 = true := by
  rw [value5, value7, value25, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(18 : Vertex), (54 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(18 : Vertex), (54 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 133 = true ∨ valuation q 3 = true ∨ valuation q 25 = true := by
  rw [value3, value7, value25, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(6 : Vertex), (54 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(6 : Vertex), (54 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value1, value8, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (32 : Vertex) (0 : Vertex) (34 : Vertex) (36 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 15 = false := by
  rw [value1, value8, value10, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (32 : Vertex) (0 : Vertex) (34 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 44 = false := by
  rw [value1, value8, value10, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (32 : Vertex) (0 : Vertex) (34 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 69 = false := by
  rw [value1, value8, value10, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (32 : Vertex) (0 : Vertex) (34 : Vertex) (288 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 15 = false := by
  rw [value1, value8, value11, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (32 : Vertex) (0 : Vertex) (36 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 44 = false := by
  rw [value1, value8, value11, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (32 : Vertex) (0 : Vertex) (36 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E121.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112121
