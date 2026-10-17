import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 9 = true ∨ valuation q 41 = true := by
  rw [value7, value9, value41, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(14 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (42 : Vertex) [(14 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 9 = true ∨ valuation q 25 = true := by
  rw [value7, value9, value25, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(14 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (138 : Vertex) [(14 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 44 = false := by
  rw [value6, value8, value26, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (9 : Vertex) (45 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 26 = true ∨ valuation q 44 = true := by
  rw [value8, value26, value44, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(45 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (9 : Vertex) [(45 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 44 = true := by
  rw [value6, value8, value44, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (45 : Vertex) → w ∈ [(9 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (45 : Vertex) [(9 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 26 = true := by
  rw [value6, value8, value26, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(9 : Vertex), (45 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (141 : Vertex) [(9 : Vertex), (45 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 9 = true := by
  rw [value9, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (14 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 4 = true ∨ valuation q 7 = true ∨ valuation q 45 = true := by
  rw [value4, value7, value9, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ∈ [(6 : Vertex), (10 : Vertex), (142 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (14 : Vertex) [(6 : Vertex), (10 : Vertex), (142 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 45 = false := by
  rw [value4, value7, value9, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (14 : Vertex) (6 : Vertex) (10 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 7 = false ∨ valuation q 45 = false := by
  rw [value7, value45, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (14 : Vertex) (10 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 4 = true ∨ valuation q 45 = true := by
  rw [value4, value9, value45, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(6 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (10 : Vertex) [(6 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value1, value10, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 15 = false := by
  rw [value1, value10, value11, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 28 = false := by
  rw [value1, value10, value11, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (48 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 46 = false := by
  rw [value1, value10, value11, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value1, value10, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (18 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 28 = false := by
  rw [value1, value10, value12, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (18 : Vertex) (48 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 46 = false := by
  rw [value1, value10, value12, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (18 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 28 = false := by
  rw [value1, value10, value15, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (24 : Vertex) (48 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 46 = false := by
  rw [value1, value10, value15, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (24 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 28 = false ∨ valuation q 46 = false := by
  rw [value1, value10, value28, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (48 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value10, value11, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 28 = false := by
  rw [value10, value11, value12, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (48 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 46 = false := by
  rw [value10, value11, value12, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 28 = false := by
  rw [value10, value11, value15, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (24 : Vertex) (48 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 46 = false := by
  rw [value10, value11, value15, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (24 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 28 = false ∨ valuation q 46 = false := by
  rw [value10, value11, value28, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (48 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 28 = false := by
  rw [value10, value12, value15, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (18 : Vertex) (24 : Vertex) (48 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 46 = false := by
  rw [value10, value12, value15, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (18 : Vertex) (24 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 46 = false := by
  rw [value10, value12, value28, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (18 : Vertex) (48 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 28 = false ∨ valuation q 46 = false := by
  rw [value10, value15, value28, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (24 : Vertex) (48 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 46 = true := by
  rw [value10, value11, value12, value15, value28, value46, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (16 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(17 : Vertex), (18 : Vertex), (24 : Vertex), (48 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (16 : Vertex) (0 : Vertex) [(17 : Vertex), (18 : Vertex), (24 : Vertex), (48 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E257.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112257
