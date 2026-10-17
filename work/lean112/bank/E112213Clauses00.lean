import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 15 = false ∨ valuation q 38 = false := by
  rw [value1, value4, value15, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (8 : Vertex) (64 : Vertex) (128 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 4 = true ∨ valuation q 15 = true ∨ valuation q 38 = true := by
  rw [value1, value4, value15, value38, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(8 : Vertex), (64 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(8 : Vertex), (64 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 2 = true ∨ valuation q 15 = true ∨ valuation q 38 = true := by
  rw [value1, value2, value15, value38, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(1 : Vertex), (64 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (8 : Vertex) [(1 : Vertex), (64 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 118 = true ∨ valuation q 2 = true ∨ valuation q 4 = true ∨ valuation q 15 = true := by
  rw [value1, value2, value4, value15, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(1 : Vertex), (8 : Vertex), (64 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (128 : Vertex) [(1 : Vertex), (8 : Vertex), (64 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 39 = false := by
  rw [value1, value2, value16, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (0 : Vertex) (65 : Vertex) (129 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 119 = true ∨ valuation q 16 = true ∨ valuation q 39 = true := by
  rw [value2, value16, value39, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(65 : Vertex), (129 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(65 : Vertex), (129 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 120 = true ∨ valuation q 10 = true := by
  rw [value3, value10, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (14 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 120 = true ∨ valuation q 7 = true := by
  rw [value3, value7, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(14 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(14 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 1 = false ∨ valuation q 6 = false ∨ valuation q 21 = false := by
  rw [value1, value4, value6, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (0 : Vertex) (12 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 6 = true ∨ valuation q 21 = true := by
  rw [value4, value6, value21, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(12 : Vertex), (72 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (0 : Vertex) [(12 : Vertex), (72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 121 = true ∨ valuation q 1 = true ∨ valuation q 21 = true := by
  rw [value1, value4, value21, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(0 : Vertex), (72 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (12 : Vertex) [(0 : Vertex), (72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 13 = false ∨ valuation q 22 = false := by
  rw [value13, value22, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (11 : Vertex) (27 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 122 = true ∨ valuation q 22 = true := by
  rw [value5, value22, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(75 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (27 : Vertex) [(75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 23 = false := by
  rw [value4, value6, value7, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (12 : Vertex) (8 : Vertex) (14 : Vertex) (76 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 123 = true ∨ valuation q 7 = true ∨ valuation q 23 = true := by
  rw [value6, value7, value23, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(14 : Vertex), (76 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (8 : Vertex) [(14 : Vertex), (76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 123 = true ∨ valuation q 4 = true ∨ valuation q 23 = true := by
  rw [value4, value6, value23, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (12 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(8 : Vertex), (76 : Vertex)] := by decide
  have hg := other_cover q (12 : Vertex) (14 : Vertex) [(8 : Vertex), (76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 25 = false := by
  rw [value3, value6, value7, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (14 : Vertex) (6 : Vertex) (12 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 25 = true := by
  rw [value6, value7, value25, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(12 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (6 : Vertex) [(12 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 48 = false := by
  rw [value8, value10, value29, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (22 : Vertex) (82 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 125 = true ∨ valuation q 29 = true ∨ valuation q 48 = true := by
  rw [value8, value29, value48, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(82 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(82 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 125 = true ∨ valuation q 10 = true ∨ valuation q 29 = true := by
  rw [value8, value10, value29, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(22 : Vertex), (82 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (146 : Vertex) [(22 : Vertex), (82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 14 = true := by
  rw [value9, value14, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (23 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value3, value8, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (6 : Vertex) (18 : Vertex) (23 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 127 = true ∨ valuation q 3 = true ∨ valuation q 11 = true := by
  rw [value3, value10, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(6 : Vertex), (23 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(6 : Vertex), (23 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 10 = true := by
  rw [value10, value11, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (21 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 9 = true := by
  rw [value9, value11, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(21 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (22 : Vertex) [(21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 129 = true ∨ valuation q 14 = true := by
  rw [value12, value14, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (27 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 129 = true ∨ valuation q 13 = true := by
  rw [value12, value13, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(27 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (29 : Vertex) [(27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 12 = true ∨ valuation q 34 = true := by
  rw [value12, value13, value34, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(25 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (11 : Vertex) [(25 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 5 = true ∨ valuation q 34 = true := by
  rw [value5, value13, value34, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(11 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (25 : Vertex) [(11 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 5 = true ∨ valuation q 12 = true := by
  rw [value5, value12, value13, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(11 : Vertex), (25 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (91 : Vertex) [(11 : Vertex), (25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 9 = false ∨ valuation q 12 = false ∨ valuation q 53 = false := by
  rw [value9, value12, value14, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (21 : Vertex) (25 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E213.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112213
