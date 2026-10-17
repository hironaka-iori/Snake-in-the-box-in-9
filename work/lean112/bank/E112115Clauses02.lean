import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 28 = false ∨ valuation q 43 = false := by
  rw [value1, value6, value28, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (72 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 18 = false := by
  rw [value6, value7, value9, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (12 : Vertex) (24 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 28 = false := by
  rw [value6, value7, value9, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (12 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 43 = false := by
  rw [value6, value7, value9, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (12 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 18 = false ∨ valuation q 28 = false := by
  rw [value6, value7, value18, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (24 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 18 = false ∨ valuation q 43 = false := by
  rw [value6, value7, value18, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (24 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 18 = false ∨ valuation q 79 = false := by
  rw [value6, value7, value18, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (24 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 28 = false ∨ valuation q 43 = false := by
  rw [value6, value7, value28, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (9 : Vertex) (72 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 28 = false := by
  rw [value6, value9, value18, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (12 : Vertex) (24 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 43 = false := by
  rw [value6, value9, value18, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (12 : Vertex) (24 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 79 = false := by
  rw [value6, value9, value18, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (12 : Vertex) (24 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 28 = false ∨ valuation q 43 = false := by
  rw [value6, value9, value28, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (12 : Vertex) (72 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 28 = false ∨ valuation q 79 = false := by
  rw [value6, value9, value28, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (12 : Vertex) (72 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 18 = false ∨ valuation q 28 = false ∨ valuation q 43 = false := by
  rw [value6, value18, value28, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (24 : Vertex) (72 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 28 = false ∨ valuation q 43 = false ∨ valuation q 79 = false := by
  rw [value6, value28, value43, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (72 : Vertex) (136 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 44 = false := by
  rw [value2, value6, value7, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (1 : Vertex) (8 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 10 = false ∨ valuation q 44 = false := by
  rw [value2, value7, value10, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (1 : Vertex) (13 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 44 = false := by
  rw [value6, value7, value10, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (8 : Vertex) (13 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 11 = false := by
  rw [value4, value7, value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (9 : Vertex) (15 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 19 = false := by
  rw [value4, value7, value8, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (9 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 19 = false := by
  rw [value4, value8, value11, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (3 : Vertex) (15 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 19 = false := by
  rw [value7, value8, value11, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (11 : Vertex) (9 : Vertex) (15 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 125 = true ∨ valuation q 7 = true ∨ valuation q 11 = true ∨ valuation q 19 = true := by
  rw [value7, value8, value11, value19, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(9 : Vertex), (15 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (3 : Vertex) [(9 : Vertex), (15 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 125 = true ∨ valuation q 4 = true ∨ valuation q 7 = true ∨ valuation q 19 = true := by
  rw [value4, value7, value8, value19, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(3 : Vertex), (9 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (15 : Vertex) [(3 : Vertex), (9 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 6 = false ∨ valuation q 10 = false ∨ valuation q 20 = false := by
  rw [value6, value9, value10, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (8 : Vertex) (13 : Vertex) (28 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 10 = true ∨ valuation q 20 = true := by
  rw [value9, value10, value20, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(13 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (8 : Vertex) [(13 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 6 = true ∨ valuation q 20 = true := by
  rw [value6, value9, value20, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(8 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (13 : Vertex) [(8 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 6 = true ∨ valuation q 10 = true := by
  rw [value6, value9, value10, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(8 : Vertex), (13 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (28 : Vertex) [(8 : Vertex), (13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 11 = false := by
  rw [value7, value9, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (9 : Vertex) (12 : Vertex) (15 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 21 = false := by
  rw [value7, value9, value10, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (9 : Vertex) (12 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 21 = false := by
  rw [value7, value10, value11, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (9 : Vertex) (15 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 21 = false := by
  rw [value9, value10, value11, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (12 : Vertex) (15 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E115.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112115
