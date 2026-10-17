import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 7 = false ∨ valuation q 9 = false := by
  rw [value7, value9, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (14 : Vertex) (12 : Vertex) (15 : Vertex) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 6 = true ∨ valuation q 9 = true := by
  rw [value6, value8, value9, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(10 : Vertex), (15 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (12 : Vertex) [(10 : Vertex), (15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 6 = true ∨ valuation q 7 = true := by
  rw [value6, value7, value8, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(10 : Vertex), (12 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (15 : Vertex) [(10 : Vertex), (12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 20 = false ∨ valuation q 29 = false := by
  rw [value8, value9, value20, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (14 : Vertex) (31 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 20 = false ∨ valuation q 78 = false := by
  rw [value8, value9, value20, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (14 : Vertex) (31 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 8 = false ∨ valuation q 29 = false ∨ valuation q 78 = false := by
  rw [value8, value9, value29, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (14 : Vertex) (79 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 20 = true ∨ valuation q 29 = true ∨ valuation q 78 = true := by
  rw [value9, value20, value29, value78, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(31 : Vertex), (79 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (14 : Vertex) [(31 : Vertex), (79 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 8 = true ∨ valuation q 29 = true ∨ valuation q 78 = true := by
  rw [value8, value9, value29, value78, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(14 : Vertex), (79 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (31 : Vertex) [(14 : Vertex), (79 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 8 = true ∨ valuation q 20 = true ∨ valuation q 78 = true := by
  rw [value8, value9, value20, value78, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(14 : Vertex), (31 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (79 : Vertex) [(14 : Vertex), (31 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 136 = true ∨ valuation q 8 = true ∨ valuation q 20 = true ∨ valuation q 29 = true := by
  rw [value8, value9, value20, value29, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(14 : Vertex), (31 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (271 : Vertex) [(14 : Vertex), (31 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value2, value10, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (19 : Vertex) (21 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 16 = false := by
  rw [value2, value10, value13, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (21 : Vertex) (25 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 137 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 16 = true := by
  rw [value10, value12, value13, value16, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(19 : Vertex), (21 : Vertex), (25 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (1 : Vertex) [(19 : Vertex), (21 : Vertex), (25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 137 = true ∨ valuation q 2 = true ∨ valuation q 13 = true ∨ valuation q 16 = true := by
  rw [value2, value10, value13, value16, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(1 : Vertex), (21 : Vertex), (25 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (19 : Vertex) [(1 : Vertex), (21 : Vertex), (25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 137 = true ∨ valuation q 2 = true ∨ valuation q 12 = true ∨ valuation q 13 = true := by
  rw [value2, value10, value12, value13, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(1 : Vertex), (19 : Vertex), (21 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (25 : Vertex) [(1 : Vertex), (19 : Vertex), (21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value3, value11, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 31 = false := by
  rw [value3, value11, value12, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (19 : Vertex) (82 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 80 = false := by
  rw [value3, value11, value12, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (19 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 31 = false := by
  rw [value3, value11, value14, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (22 : Vertex) (82 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 80 = false := by
  rw [value3, value11, value14, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (22 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 31 = false ∨ valuation q 80 = false := by
  rw [value3, value11, value31, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (82 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 80 = false := by
  rw [value11, value12, value31, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (19 : Vertex) (82 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 12 = true ∨ valuation q 14 = true ∨ valuation q 31 = true ∨ valuation q 80 = true := by
  rw [value11, value12, value14, value31, value80, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(19 : Vertex), (22 : Vertex), (82 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (2 : Vertex) [(19 : Vertex), (22 : Vertex), (82 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 3 = true ∨ valuation q 12 = true ∨ valuation q 14 = true ∨ valuation q 80 = true := by
  rw [value3, value11, value12, value14, value80, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(2 : Vertex), (19 : Vertex), (22 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (82 : Vertex) [(2 : Vertex), (19 : Vertex), (22 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = true ∨ valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 17 = true := by
  rw [value10, value11, value12, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ∈ [(17 : Vertex), (18 : Vertex), (23 : Vertex), (27 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (19 : Vertex) [(17 : Vertex), (18 : Vertex), (23 : Vertex), (27 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 15 = false := by
  rw [value10, value11, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (17 : Vertex) (18 : Vertex) (23 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 17 = false := by
  rw [value10, value11, value12, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (17 : Vertex) (18 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value10, value12, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (17 : Vertex) (23 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value11, value12, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (18 : Vertex) (23 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value15, value17, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (19 : Vertex) (23 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true ∨ valuation q 10 = true ∨ valuation q 11 = true ∨ valuation q 17 = true := by
  rw [value10, value11, value12, value17, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(17 : Vertex), (18 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (23 : Vertex) [(17 : Vertex), (18 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true ∨ valuation q 10 = true ∨ valuation q 11 = true ∨ valuation q 15 = true := by
  rw [value10, value11, value12, value15, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(17 : Vertex), (18 : Vertex), (23 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (27 : Vertex) [(17 : Vertex), (18 : Vertex), (23 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E057.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112057
