import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 6 = true ∨ valuation q 26 = true := by
  rw [value6, value8, value26, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(72 : Vertex), (108 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (204 : Vertex) [(72 : Vertex), (108 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 46 = false := by
  rw [value5, value7, value9, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 7 = true ∨ valuation q 46 = true := by
  rw [value7, value9, value46, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(75 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (71 : Vertex) [(75 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 5 = true ∨ valuation q 46 = true := by
  rw [value5, value9, value46, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(71 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (75 : Vertex) [(71 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 5 = true ∨ valuation q 7 = true := by
  rw [value5, value7, value9, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(71 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (207 : Vertex) [(71 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 10 = true := by
  rw [value10, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (80 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 47 = true := by
  rw [value10, value11, value13, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ∈ [(81 : Vertex), (84 : Vertex), (208 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (80 : Vertex) [(81 : Vertex), (84 : Vertex), (208 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 47 = false := by
  rw [value10, value11, value13, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (81 : Vertex) (84 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 13 = false ∨ valuation q 47 = false := by
  rw [value13, value47, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (80 : Vertex) (84 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 137 = true ∨ valuation q 13 = true ∨ valuation q 47 = true := by
  rw [value10, value13, value47, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(84 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (81 : Vertex) [(84 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 137 = true ∨ valuation q 11 = true ∨ valuation q 47 = true := by
  rw [value10, value11, value47, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(81 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (84 : Vertex) [(81 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 137 = true ∨ valuation q 11 = true ∨ valuation q 13 = true := by
  rw [value10, value11, value13, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(81 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (208 : Vertex) [(81 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 12 = false := by
  rw [value1, value10, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (80 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 15 = false := by
  rw [value1, value10, value11, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (80 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 28 = false := by
  rw [value1, value10, value11, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (80 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 48 = false := by
  rw [value1, value10, value11, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (80 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 89 = false := by
  rw [value1, value10, value11, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (80 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value1, value11, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (83 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 28 = false := by
  rw [value1, value11, value12, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (83 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 48 = false := by
  rw [value1, value11, value12, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (83 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 12 = false ∨ valuation q 89 = false := by
  rw [value1, value11, value12, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (83 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 28 = false := by
  rw [value1, value11, value15, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (89 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 48 = false := by
  rw [value1, value11, value15, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (89 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 89 = false := by
  rw [value1, value11, value15, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (89 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 28 = false ∨ valuation q 48 = false := by
  rw [value1, value11, value28, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (113 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 28 = false ∨ valuation q 89 = false := by
  rw [value1, value11, value28, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (113 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 1 = false ∨ valuation q 48 = false ∨ valuation q 89 = false := by
  rw [value1, value11, value48, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (209 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value10, value11, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (83 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 28 = false := by
  rw [value10, value11, value12, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (83 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 48 = false := by
  rw [value10, value11, value12, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (83 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 89 = false := by
  rw [value10, value11, value12, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (83 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 28 = false := by
  rw [value10, value11, value15, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (89 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E260.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112260
