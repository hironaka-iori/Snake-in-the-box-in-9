import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 114 = true ∨ valuation q 3 = true ∨ valuation q 7 = true ∨ valuation q 13 = true ∨ valuation q 64 = true := by
  rw [value3, value4, value7, value13, value64, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(2 : Vertex), (11 : Vertex), (19 : Vertex), (259 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (1 : Vertex) [(2 : Vertex), (11 : Vertex), (19 : Vertex), (259 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 114 = true ∨ valuation q 2 = true ∨ valuation q 3 = true ∨ valuation q 7 = true ∨ valuation q 64 = true := by
  rw [value2, value3, value4, value7, value64, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(1 : Vertex), (2 : Vertex), (11 : Vertex), (259 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (19 : Vertex) [(1 : Vertex), (2 : Vertex), (11 : Vertex), (259 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 22 = false := by
  rw [value2, value5, value8, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (13 : Vertex) (69 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 66 = false := by
  rw [value2, value5, value8, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (13 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 2 = false ∨ valuation q 22 = false ∨ valuation q 66 = false := by
  rw [value2, value5, value22, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (69 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 115 = true ∨ valuation q 8 = true ∨ valuation q 22 = true ∨ valuation q 66 = true := by
  rw [value5, value8, value22, value66, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(13 : Vertex), (69 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (1 : Vertex) [(13 : Vertex), (69 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 115 = true ∨ valuation q 2 = true ∨ valuation q 22 = true ∨ valuation q 66 = true := by
  rw [value2, value5, value22, value66, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(1 : Vertex), (69 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (13 : Vertex) [(1 : Vertex), (69 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 115 = true ∨ valuation q 2 = true ∨ valuation q 8 = true ∨ valuation q 66 = true := by
  rw [value2, value5, value8, value66, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(1 : Vertex), (13 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (69 : Vertex) [(1 : Vertex), (13 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 115 = true ∨ valuation q 2 = true ∨ valuation q 8 = true ∨ valuation q 22 = true := by
  rw [value2, value5, value8, value22, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(1 : Vertex), (13 : Vertex), (69 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (261 : Vertex) [(1 : Vertex), (13 : Vertex), (69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value3, value6, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (2 : Vertex) (22 : Vertex) (70 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 116 = true ∨ valuation q 3 = true ∨ valuation q 23 = true := by
  rw [value3, value6, value23, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(2 : Vertex), (70 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(2 : Vertex), (70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 116 = true ∨ valuation q 3 = true ∨ valuation q 14 = true := by
  rw [value3, value6, value14, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(2 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (70 : Vertex) [(2 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 24 = false := by
  rw [value4, value7, value9, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (15 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 68 = false := by
  rw [value4, value7, value9, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (15 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 4 = false ∨ valuation q 24 = false ∨ valuation q 68 = false := by
  rw [value4, value7, value24, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (75 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 24 = false ∨ valuation q 68 = false := by
  rw [value7, value9, value24, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (15 : Vertex) (75 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 117 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 68 = true := by
  rw [value4, value7, value9, value68, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(3 : Vertex), (15 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (75 : Vertex) [(3 : Vertex), (15 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 17 = false := by
  rw [value5, value8, value9, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (5 : Vertex) (15 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 118 = true ∨ valuation q 5 = true ∨ valuation q 17 = true := by
  rw [value5, value8, value17, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(5 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (15 : Vertex) [(5 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 118 = true ∨ valuation q 5 = true ∨ valuation q 9 = true := by
  rw [value5, value8, value9, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(5 : Vertex), (15 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (29 : Vertex) [(5 : Vertex), (15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 19 = false := by
  rw [value7, value8, value9, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (11 : Vertex) (13 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 119 = true ∨ valuation q 8 = true ∨ valuation q 19 = true := by
  rw [value8, value9, value19, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(13 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (11 : Vertex) [(13 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 119 = true ∨ valuation q 7 = true ∨ valuation q 19 = true := by
  rw [value7, value9, value19, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(11 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (13 : Vertex) [(11 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 119 = true ∨ valuation q 7 = true ∨ valuation q 8 = true := by
  rw [value7, value8, value9, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(11 : Vertex), (13 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (31 : Vertex) [(11 : Vertex), (13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value1, value10, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 15 = false := by
  rw [value1, value10, value11, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 71 = false := by
  rw [value1, value10, value11, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value1, value10, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (18 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 71 = false := by
  rw [value1, value10, value12, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (18 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 71 = false := by
  rw [value1, value10, value15, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (24 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value10, value11, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 71 = false := by
  rw [value10, value11, value12, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E123.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112123
