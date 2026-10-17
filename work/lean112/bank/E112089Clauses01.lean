import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 24 = false ∨ valuation q 41 = false := by
  rw [value6, value8, value24, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (11 : Vertex) (73 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 24 = false ∨ valuation q 41 = false := by
  rw [value6, value9, value24, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (13 : Vertex) (73 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 2 = true ∨ valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 24 = true := by
  rw [value2, value6, value8, value9, value24, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (9 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(1 : Vertex), (11 : Vertex), (13 : Vertex), (73 : Vertex)] := by decide
  have hg := other_cover q (9 : Vertex) (137 : Vertex) [(1 : Vertex), (11 : Vertex), (13 : Vertex), (73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 42 = false := by
  rw [value7, value8, value10, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (11 : Vertex) (14 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 81 = false := by
  rw [value7, value8, value10, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (11 : Vertex) (14 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 42 = false ∨ valuation q 81 = false := by
  rw [value7, value8, value42, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (11 : Vertex) (138 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 10 = false ∨ valuation q 42 = false ∨ valuation q 81 = false := by
  rw [value7, value10, value42, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (14 : Vertex) (138 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 131 = true ∨ valuation q 10 = true ∨ valuation q 42 = true ∨ valuation q 81 = true := by
  rw [value7, value10, value42, value81, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(14 : Vertex), (138 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (11 : Vertex) [(14 : Vertex), (138 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 131 = true ∨ valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 42 = true := by
  rw [value7, value8, value10, value42, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(11 : Vertex), (14 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (266 : Vertex) [(11 : Vertex), (14 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 43 = true := by
  rw [value3, value6, value7, value8, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ∈ [(3 : Vertex), (9 : Vertex), (10 : Vertex), (139 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (11 : Vertex) [(3 : Vertex), (9 : Vertex), (10 : Vertex), (139 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value3, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (9 : Vertex) (10 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 43 = false := by
  rw [value3, value6, value8, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (9 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 43 = false := by
  rw [value3, value7, value8, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (10 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 43 = false := by
  rw [value6, value7, value8, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (9 : Vertex) (10 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 43 = true := by
  rw [value6, value7, value8, value43, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(9 : Vertex), (10 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (3 : Vertex) [(9 : Vertex), (10 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 3 = true ∨ valuation q 7 = true ∨ valuation q 43 = true := by
  rw [value3, value7, value8, value43, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(3 : Vertex), (10 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (9 : Vertex) [(3 : Vertex), (10 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 43 = true := by
  rw [value3, value6, value8, value43, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(3 : Vertex), (9 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (10 : Vertex) [(3 : Vertex), (9 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 7 = true := by
  rw [value3, value6, value7, value8, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(3 : Vertex), (9 : Vertex), (10 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (139 : Vertex) [(3 : Vertex), (9 : Vertex), (10 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 4 = true ∨ valuation q 6 = true ∨ valuation q 16 = true := by
  rw [value4, value6, value9, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ∈ [(5 : Vertex), (9 : Vertex), (29 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (13 : Vertex) [(5 : Vertex), (9 : Vertex), (29 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 16 = false := by
  rw [value4, value6, value9, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (5 : Vertex) (9 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 4 = false ∨ valuation q 16 = false := by
  rw [value4, value16, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (13 : Vertex) (5 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 133 = true ∨ valuation q 6 = true ∨ valuation q 16 = true := by
  rw [value6, value9, value16, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(9 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (5 : Vertex) [(9 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 133 = true ∨ valuation q 4 = true ∨ valuation q 16 = true := by
  rw [value4, value9, value16, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(5 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (9 : Vertex) [(5 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 133 = true ∨ valuation q 4 = true ∨ valuation q 6 = true := by
  rw [value4, value6, value9, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(5 : Vertex), (9 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (29 : Vertex) [(5 : Vertex), (9 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = true ∨ valuation q 17 = true ∨ valuation q 26 = true := by
  rw [value7, value10, value17, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ∈ [(10 : Vertex), (30 : Vertex), (78 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (14 : Vertex) [(10 : Vertex), (30 : Vertex), (78 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 17 = false ∨ valuation q 26 = false := by
  rw [value7, value10, value17, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (14 : Vertex) (10 : Vertex) (30 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 7 = false ∨ valuation q 17 = false := by
  rw [value7, value17, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (14 : Vertex) (10 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 17 = true ∨ valuation q 26 = true := by
  rw [value10, value17, value26, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(30 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (10 : Vertex) [(30 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 7 = true ∨ valuation q 26 = true := by
  rw [value7, value10, value26, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(10 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (30 : Vertex) [(10 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 7 = true ∨ valuation q 17 = true := by
  rw [value7, value10, value17, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(10 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (78 : Vertex) [(10 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = true ∨ valuation q 12 = true := by
  rw [value1, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (16 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (18 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (16 : Vertex) [(0 : Vertex), (18 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 1 = false ∨ valuation q 12 = false := by
  rw [value1, value12, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (16 : Vertex) (0 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E089.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112089
