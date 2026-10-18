import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 24 = false ∨ valuation q 39 = false := by
  rw [value2, value7, value24, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (9 : Vertex) (65 : Vertex) (129 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 24 = false ∨ valuation q 74 = false := by
  rw [value2, value7, value24, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (9 : Vertex) (65 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 39 = false ∨ valuation q 74 = false := by
  rw [value2, value7, value39, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (9 : Vertex) (129 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 39 = false := by
  rw [value2, value13, value24, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (17 : Vertex) (65 : Vertex) (129 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 74 = false := by
  rw [value2, value13, value24, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (17 : Vertex) (65 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 39 = false ∨ valuation q 74 = false := by
  rw [value2, value13, value39, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (17 : Vertex) (129 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 24 = false ∨ valuation q 39 = false ∨ valuation q 74 = false := by
  rw [value2, value24, value39, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (65 : Vertex) (129 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 14 = false := by
  rw [value1, value3, value4, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (2 : Vertex) (0 : Vertex) (3 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 5 = false := by
  rw [value2, value3, value4, value5]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (1 : Vertex) (2 : Vertex) (7 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 8 = false := by
  rw [value2, value4, value5, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (1 : Vertex) (7 : Vertex) (11 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 15 = false := by
  rw [value2, value4, value5, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (1 : Vertex) (7 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 15 = false := by
  rw [value3, value4, value5, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (3 : Vertex) (2 : Vertex) (7 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 2 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 15 = true := by
  rw [value2, value4, value5, value8, value15, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(1 : Vertex), (7 : Vertex), (11 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (2 : Vertex) [(1 : Vertex), (7 : Vertex), (11 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 2 = true ∨ valuation q 3 = true ∨ valuation q 8 = true ∨ valuation q 15 = true := by
  rw [value2, value3, value4, value8, value15, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(1 : Vertex), (2 : Vertex), (11 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (7 : Vertex) [(1 : Vertex), (2 : Vertex), (11 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 2 = true ∨ valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 15 = true := by
  rw [value2, value3, value4, value5, value15, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (3 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(1 : Vertex), (2 : Vertex), (7 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (3 : Vertex) (11 : Vertex) [(1 : Vertex), (2 : Vertex), (7 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = true ∨ valuation q 11 = true ∨ valuation q 78 = true := by
  rw [value4, value5, value11, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ∈ [(3 : Vertex), (15 : Vertex), (263 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (7 : Vertex) [(3 : Vertex), (15 : Vertex), (263 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 78 = false := by
  rw [value4, value5, value11, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (7 : Vertex) (3 : Vertex) (15 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 11 = true ∨ valuation q 78 = true := by
  rw [value5, value11, value78, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(15 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (3 : Vertex) [(15 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 4 = true ∨ valuation q 78 = true := by
  rw [value4, value5, value78, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(3 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (15 : Vertex) [(3 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value4, value5, value11, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(3 : Vertex), (15 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (263 : Vertex) [(3 : Vertex), (15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 9 = false := by
  rw [value1, value6, value7, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (12 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 18 = false := by
  rw [value1, value6, value7, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 28 = false := by
  rw [value1, value6, value7, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 43 = false := by
  rw [value1, value6, value7, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 79 = false := by
  rw [value1, value6, value7, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (9 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 18 = false := by
  rw [value1, value6, value9, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (12 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 28 = false := by
  rw [value1, value6, value9, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (12 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 43 = false := by
  rw [value1, value6, value9, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (12 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 79 = false := by
  rw [value1, value6, value9, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (12 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 18 = false ∨ valuation q 28 = false := by
  rw [value1, value6, value18, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (24 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 18 = false ∨ valuation q 43 = false := by
  rw [value1, value6, value18, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (24 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 18 = false ∨ valuation q 79 = false := by
  rw [value1, value6, value18, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (24 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E115.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112115
