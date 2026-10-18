import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 71 = false := by
  rw [value10, value11, value15, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (17 : Vertex) (24 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 71 = false := by
  rw [value10, value12, value15, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (18 : Vertex) (24 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 120 = true ∨ valuation q 1 = true ∨ valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 71 = true := by
  rw [value1, value10, value11, value12, value71, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (16 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(0 : Vertex), (17 : Vertex), (18 : Vertex), (272 : Vertex)] := by decide
  have hg := other_cover q (16 : Vertex) (24 : Vertex) [(0 : Vertex), (17 : Vertex), (18 : Vertex), (272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 2 = false ∨ valuation q 10 = false ∨ valuation q 13 = false := by
  rw [value2, value10, value11, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (16 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 121 = true ∨ valuation q 10 = true ∨ valuation q 13 = true := by
  rw [value10, value11, value13, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(16 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (1 : Vertex) [(16 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 121 = true ∨ valuation q 2 = true ∨ valuation q 13 = true := by
  rw [value2, value11, value13, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(1 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (16 : Vertex) [(1 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 121 = true ∨ valuation q 2 = true ∨ valuation q 10 = true := by
  rw [value2, value10, value11, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(1 : Vertex), (16 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (19 : Vertex) [(1 : Vertex), (16 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 13 = false := by
  rw [value3, value10, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (16 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 14 = false := by
  rw [value3, value10, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (16 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value3, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value10, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (16 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 122 = true ∨ valuation q 3 = true ∨ valuation q 10 = true ∨ valuation q 14 = true := by
  rw [value3, value10, value12, value14, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(2 : Vertex), (16 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (19 : Vertex) [(2 : Vertex), (16 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 122 = true ∨ valuation q 3 = true ∨ valuation q 10 = true ∨ valuation q 13 = true := by
  rw [value3, value10, value12, value13, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(2 : Vertex), (16 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(2 : Vertex), (16 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = true ∨ valuation q 11 = true ∨ valuation q 12 = true := by
  rw [value4, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ∈ [(3 : Vertex), (17 : Vertex), (18 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (19 : Vertex) [(3 : Vertex), (17 : Vertex), (18 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value4, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (3 : Vertex) (17 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 123 = true ∨ valuation q 4 = true ∨ valuation q 12 = true := by
  rw [value4, value12, value13, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(3 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (17 : Vertex) [(3 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 18 = false := by
  rw [value6, value12, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (6 : Vertex) (18 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 12 = true := by
  rw [value6, value12, value14, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(6 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (30 : Vertex) [(6 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 10 = false ∨ valuation q 16 = false ∨ valuation q 75 = false := by
  rw [value10, value15, value16, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (24 : Vertex) (16 : Vertex) (28 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 125 = true ∨ valuation q 16 = true ∨ valuation q 75 = true := by
  rw [value15, value16, value75, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(28 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (16 : Vertex) [(28 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 125 = true ∨ valuation q 10 = true ∨ valuation q 75 = true := by
  rw [value10, value15, value75, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(16 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (28 : Vertex) [(16 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 125 = true ∨ valuation q 10 = true ∨ valuation q 16 = true := by
  rw [value10, value15, value16, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(16 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (280 : Vertex) [(16 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value15, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (24 : Vertex) (29 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 17 = true ∨ valuation q 18 = true := by
  rw [value16, value17, value18, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(29 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (24 : Vertex) [(29 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value15, value16, value18, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(24 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (29 : Vertex) [(24 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 15 = true ∨ valuation q 17 = true := by
  rw [value15, value16, value17, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(24 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(24 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 127 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value16, value17, value19, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(28 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (13 : Vertex) [(28 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 127 = true ∨ valuation q 8 = true ∨ valuation q 19 = true := by
  rw [value8, value17, value19, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(13 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (28 : Vertex) [(13 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 128 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value16, value18, value19, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(28 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (22 : Vertex) [(28 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 128 = true ∨ valuation q 14 = true ∨ valuation q 19 = true := by
  rw [value14, value18, value19, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(22 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (28 : Vertex) [(22 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 128 = true ∨ valuation q 14 = true ∨ valuation q 16 = true := by
  rw [value14, value16, value18, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(22 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (31 : Vertex) [(22 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value9, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E123.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112123
