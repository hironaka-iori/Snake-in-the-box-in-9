import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 74 = false := by
  rw [value1, value5, value7, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (12 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 26 = false ∨ valuation q 74 = false := by
  rw [value1, value5, value26, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (72 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 26 = false := by
  rw [value5, value6, value7, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (10 : Vertex) (12 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 74 = false := by
  rw [value5, value6, value7, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (10 : Vertex) (12 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 43 = false := by
  rw [value5, value6, value26, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (10 : Vertex) (72 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 74 = false := by
  rw [value5, value6, value26, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (10 : Vertex) (72 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 43 = false := by
  rw [value5, value7, value26, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (12 : Vertex) (72 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 74 = false := by
  rw [value5, value7, value26, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (12 : Vertex) (72 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 8 = false := by
  rw [value3, value5, value6, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (2 : Vertex) (8 : Vertex) (14 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 45 = false := by
  rw [value3, value6, value8, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (2 : Vertex) (14 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 45 = false := by
  rw [value5, value6, value8, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (8 : Vertex) (14 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 134 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 45 = true := by
  rw [value5, value6, value8, value45, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(8 : Vertex), (14 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (2 : Vertex) [(8 : Vertex), (14 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 134 = true ∨ valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 45 = true := by
  rw [value3, value5, value6, value45, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(2 : Vertex), (8 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (14 : Vertex) [(2 : Vertex), (8 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 18 = false := by
  rw [value5, value7, value8, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (8 : Vertex) (14 : Vertex) (28 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 77 = false := by
  rw [value5, value7, value8, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (8 : Vertex) (14 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = false ∨ valuation q 18 = false ∨ valuation q 77 = false := by
  rw [value5, value7, value18, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (8 : Vertex) (28 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 18 = false ∨ valuation q 77 = false := by
  rw [value7, value8, value18, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (14 : Vertex) (28 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 135 = true ∨ valuation q 5 = true ∨ valuation q 18 = true ∨ valuation q 77 = true := by
  rw [value5, value7, value18, value77, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(8 : Vertex), (28 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (14 : Vertex) [(8 : Vertex), (28 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 135 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 77 = true := by
  rw [value5, value7, value8, value77, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(8 : Vertex), (14 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (28 : Vertex) [(8 : Vertex), (14 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 9 = true := by
  rw [value6, value7, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ∈ [(10 : Vertex), (12 : Vertex), (15 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (14 : Vertex) [(10 : Vertex), (12 : Vertex), (15 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 9 = false := by
  rw [value6, value7, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (14 : Vertex) (10 : Vertex) (12 : Vertex) (15 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 136 = true ∨ valuation q 7 = true ∨ valuation q 9 = true := by
  rw [value7, value8, value9, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(12 : Vertex), (15 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (10 : Vertex) [(12 : Vertex), (15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 136 = true ∨ valuation q 6 = true ∨ valuation q 9 = true := by
  rw [value6, value8, value9, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(10 : Vertex), (15 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (12 : Vertex) [(10 : Vertex), (15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 136 = true ∨ valuation q 6 = true ∨ valuation q 7 = true := by
  rw [value6, value7, value8, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(10 : Vertex), (12 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (15 : Vertex) [(10 : Vertex), (12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 20 = false ∨ valuation q 29 = false := by
  rw [value8, value9, value20, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (14 : Vertex) (31 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 20 = false ∨ valuation q 79 = false := by
  rw [value8, value9, value20, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (14 : Vertex) (31 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 29 = false ∨ valuation q 79 = false := by
  rw [value8, value9, value29, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (14 : Vertex) (79 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 20 = false ∨ valuation q 29 = false ∨ valuation q 79 = false := by
  rw [value9, value20, value29, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (31 : Vertex) (79 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 137 = true ∨ valuation q 20 = true ∨ valuation q 29 = true ∨ valuation q 79 = true := by
  rw [value9, value20, value29, value79, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(31 : Vertex), (79 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (14 : Vertex) [(31 : Vertex), (79 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 137 = true ∨ valuation q 8 = true ∨ valuation q 29 = true ∨ valuation q 79 = true := by
  rw [value8, value9, value29, value79, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(14 : Vertex), (79 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (31 : Vertex) [(14 : Vertex), (79 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value2, value10, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (19 : Vertex) (21 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 16 = false := by
  rw [value2, value10, value12, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (19 : Vertex) (25 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E055.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112055
