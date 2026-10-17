import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 135 = true ∨ valuation q 12 = true := by
  rw [value11, value12, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (16 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(18 : Vertex)] := by decide
  have hg := other_cover q (16 : Vertex) (0 : Vertex) [(18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 135 = true ∨ valuation q 1 = true := by
  rw [value1, value11, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (16 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (16 : Vertex) (18 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value11, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (16 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 13 = true ∨ valuation q 14 = true := by
  rw [value12, value13, value14, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(19 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (16 : Vertex) [(19 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 11 = true ∨ valuation q 14 = true := by
  rw [value11, value12, value14, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(16 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (19 : Vertex) [(16 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 11 = true ∨ valuation q 13 = true := by
  rw [value11, value12, value13, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(16 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(16 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 13 = true := by
  rw [value13, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (19 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true ∨ valuation q 12 = true ∨ valuation q 28 = true := by
  rw [value12, value13, value28, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(18 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (3 : Vertex) [(18 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true ∨ valuation q 3 = true ∨ valuation q 28 = true := by
  rw [value3, value13, value28, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(3 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (18 : Vertex) [(3 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true ∨ valuation q 3 = true ∨ valuation q 12 = true := by
  rw [value3, value12, value13, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(3 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (83 : Vertex) [(3 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 14 = true := by
  rw [value14, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (22 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 17 = false ∨ valuation q 49 = false := by
  rw [value12, value14, value17, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (18 : Vertex) (30 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 17 = true ∨ valuation q 49 = true := by
  rw [value14, value17, value49, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(30 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(30 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 12 = true ∨ valuation q 49 = true := by
  rw [value12, value14, value49, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(18 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (30 : Vertex) [(18 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 12 = true ∨ valuation q 17 = true := by
  rw [value12, value14, value17, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(18 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (150 : Vertex) [(18 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 15 = true := by
  rw [value15, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (28 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = true ∨ valuation q 17 = true := by
  rw [value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ∈ [(29 : Vertex), (30 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (28 : Vertex) [(29 : Vertex), (30 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 139 = true ∨ valuation q 17 = true := by
  rw [value15, value17, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (29 : Vertex) [(30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 139 = true ∨ valuation q 16 = true := by
  rw [value15, value16, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 15 = true := by
  rw [value15, value16, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(28 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (13 : Vertex) [(28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 9 = true := by
  rw [value9, value16, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(13 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (28 : Vertex) [(13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 10 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value10, value14, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (30 : Vertex) (14 : Vertex) (22 : Vertex) (28 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 14 = true ∨ valuation q 15 = true := by
  rw [value14, value15, value17, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(22 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (14 : Vertex) [(22 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 141 = true ∨ valuation q 10 = true ∨ valuation q 14 = true := by
  rw [value10, value14, value17, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(14 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (28 : Vertex) [(14 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 1 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value1, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (65 : Vertex) (66 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 1 = false ∨ valuation q 19 = false ∨ valuation q 21 = false := by
  rw [value1, value18, value19, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (65 : Vertex) (68 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 1 = false ∨ valuation q 20 = false ∨ valuation q 23 = false := by
  rw [value1, value18, value20, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (66 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 1 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value1, value18, value21, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (68 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value18, value19, value21, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (68 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value18, value20, value21, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (66 : Vertex) (68 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 23 = true := by
  rw [value18, value19, value20, value21, value23, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (64 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(65 : Vertex), (66 : Vertex), (68 : Vertex), (72 : Vertex)] := by decide
  have hg := other_cover q (64 : Vertex) (0 : Vertex) [(65 : Vertex), (66 : Vertex), (68 : Vertex), (72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 2 = false ∨ valuation q 18 = false ∨ valuation q 24 = false := by
  rw [value2, value18, value19, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (64 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E089.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112089
