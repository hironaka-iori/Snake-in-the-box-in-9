import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 5 = true := by
  rw [value1, value5, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(8 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(8 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 117 = true ∨ valuation q 2 = true := by
  rw [value1, value2, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(1 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (8 : Vertex) [(1 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 17 = false := by
  rw [value1, value2, value9, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (1 : Vertex) (0 : Vertex) (17 : Vertex) (65 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 9 = true ∨ valuation q 17 = true := by
  rw [value2, value9, value17, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(17 : Vertex), (65 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(17 : Vertex), (65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 1 = true ∨ valuation q 17 = true := by
  rw [value1, value2, value17, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex), (65 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex), (65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 118 = true ∨ valuation q 1 = true ∨ valuation q 9 = true := by
  rw [value1, value2, value9, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(0 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (65 : Vertex) [(0 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 7 = true ∨ valuation q 12 = true := by
  rw [value3, value7, value12, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(14 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (7 : Vertex) [(14 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 4 = true ∨ valuation q 12 = true := by
  rw [value3, value4, value12, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(7 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (14 : Vertex) [(7 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 119 = true ∨ valuation q 4 = true ∨ valuation q 7 = true := by
  rw [value3, value4, value7, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(7 : Vertex), (14 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(7 : Vertex), (14 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 120 = true ∨ valuation q 8 = true := by
  rw [value4, value8, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(15 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (6 : Vertex) [(15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 120 = true ∨ valuation q 3 = true := by
  rw [value3, value4, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (15 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 6 = true := by
  rw [value5, value6, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(10 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (0 : Vertex) [(10 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 1 = true := by
  rw [value1, value5, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (10 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 14 = false := by
  rw [value5, value6, value7, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (8 : Vertex) (14 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 7 = true ∨ valuation q 14 = true := by
  rw [value6, value7, value14, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(14 : Vertex), (26 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (8 : Vertex) [(14 : Vertex), (26 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 5 = true ∨ valuation q 14 = true := by
  rw [value5, value6, value14, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(8 : Vertex), (26 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (14 : Vertex) [(8 : Vertex), (26 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 5 = true ∨ valuation q 7 = true := by
  rw [value5, value6, value7, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (26 : Vertex) → w ∈ [(8 : Vertex), (14 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (26 : Vertex) [(8 : Vertex), (14 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 8 = false := by
  rw [value3, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (14 : Vertex) (6 : Vertex) (10 : Vertex) (15 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value3, value6, value7, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(6 : Vertex), (10 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (15 : Vertex) [(6 : Vertex), (10 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 7 = true ∨ valuation q 21 = true := by
  rw [value7, value8, value21, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(14 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (7 : Vertex) [(14 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 4 = true ∨ valuation q 21 = true := by
  rw [value4, value8, value21, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (15 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(7 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (15 : Vertex) (14 : Vertex) [(7 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 11 = false ∨ valuation q 13 = false := by
  rw [value2, value9, value11, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (21 : Vertex) (25 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 2 = true ∨ valuation q 13 = true := by
  rw [value2, value9, value13, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(1 : Vertex), (25 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (21 : Vertex) [(1 : Vertex), (25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 2 = true ∨ valuation q 11 = true := by
  rw [value2, value9, value11, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(1 : Vertex), (21 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (25 : Vertex) [(1 : Vertex), (21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 12 = true := by
  rw [value10, value12, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (20 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (20 : Vertex) (21 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 11 = true := by
  rw [value10, value11, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (20 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(21 : Vertex)] := by decide
  have hg := other_cover q (20 : Vertex) (22 : Vertex) [(21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 10 = true ∨ valuation q 16 = true := by
  rw [value10, value11, value16, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(20 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (17 : Vertex) [(20 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 9 = true ∨ valuation q 16 = true := by
  rw [value9, value11, value16, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (20 : Vertex) → w ∈ [(17 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (20 : Vertex) [(17 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 9 = true ∨ valuation q 10 = true := by
  rw [value9, value10, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(17 : Vertex), (20 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (29 : Vertex) [(17 : Vertex), (20 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 10 = true := by
  rw [value10, value12, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(20 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(20 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 3 = true := by
  rw [value3, value12, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (20 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (20 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 129 = true ∨ valuation q 15 = true ∨ valuation q 16 = true := by
  rw [value13, value15, value16, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(27 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (17 : Vertex) [(27 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E051.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112051
