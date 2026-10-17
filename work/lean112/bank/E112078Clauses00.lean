import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 7 = false := by
  rw [value1, value2, value5, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (67 : Vertex) (70 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 39 = false := by
  rw [value1, value2, value7, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (67 : Vertex) (74 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 39 = false := by
  rw [value1, value5, value7, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (70 : Vertex) (74 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 120 = true ∨ valuation q 5 = true ∨ valuation q 7 = true ∨ valuation q 39 = true := by
  rw [value1, value5, value7, value39, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(70 : Vertex), (74 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (67 : Vertex) [(70 : Vertex), (74 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 120 = true ∨ valuation q 2 = true ∨ valuation q 5 = true ∨ valuation q 39 = true := by
  rw [value1, value2, value5, value39, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(67 : Vertex), (70 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (74 : Vertex) [(67 : Vertex), (70 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 121 = true ∨ valuation q 40 = true := by
  rw [value2, value40, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(195 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (66 : Vertex) [(195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 121 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(66 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (195 : Vertex) [(66 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 11 = true := by
  rw [value3, value4, value5, value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ∈ [(69 : Vertex), (70 : Vertex), (76 : Vertex), (84 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (68 : Vertex) [(69 : Vertex), (70 : Vertex), (76 : Vertex), (84 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 8 = false := by
  rw [value3, value4, value5, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (69 : Vertex) (70 : Vertex) (76 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 11 = false := by
  rw [value3, value4, value5, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (69 : Vertex) (70 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value3, value4, value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (69 : Vertex) (76 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value3, value5, value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (70 : Vertex) (76 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 4 = false ∨ valuation q 11 = false := by
  rw [value4, value11, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (68 : Vertex) (69 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 122 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 11 = true := by
  rw [value3, value5, value8, value11, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(70 : Vertex), (76 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (69 : Vertex) [(70 : Vertex), (76 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 122 = true ∨ valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 11 = true := by
  rw [value3, value4, value5, value11, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(69 : Vertex), (70 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (76 : Vertex) [(69 : Vertex), (70 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 122 = true ∨ valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 8 = true := by
  rw [value3, value4, value5, value8, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(69 : Vertex), (70 : Vertex), (76 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(69 : Vertex), (70 : Vertex), (76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 41 = false := by
  rw [value3, value4, value12, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (85 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 123 = true ∨ valuation q 12 = true ∨ valuation q 41 = true := by
  rw [value4, value12, value41, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(85 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (68 : Vertex) [(85 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 123 = true ∨ valuation q 3 = true ∨ valuation q 41 = true := by
  rw [value3, value4, value41, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(68 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (85 : Vertex) [(68 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 123 = true ∨ valuation q 3 = true ∨ valuation q 12 = true := by
  rw [value3, value4, value12, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(68 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (197 : Vertex) [(68 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 71 = false := by
  rw [value1, value5, value9, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (66 : Vertex) (78 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 124 = true ∨ valuation q 3 = true ∨ valuation q 9 = true ∨ valuation q 71 = true := by
  rw [value3, value5, value9, value71, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(68 : Vertex), (78 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (66 : Vertex) [(68 : Vertex), (78 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 3 = true ∨ valuation q 71 = true := by
  rw [value1, value3, value5, value71, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(66 : Vertex), (68 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (78 : Vertex) [(66 : Vertex), (68 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 124 = true ∨ valuation q 1 = true ∨ valuation q 3 = true ∨ valuation q 9 = true := by
  rw [value1, value3, value5, value9, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(66 : Vertex), (68 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (326 : Vertex) [(66 : Vertex), (68 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 125 = true ∨ valuation q 43 = true ∨ valuation q 74 = true := by
  rw [value6, value43, value74, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(201 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (89 : Vertex) [(201 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 125 = true ∨ valuation q 15 = true ∨ valuation q 74 = true := by
  rw [value6, value15, value74, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(89 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (201 : Vertex) [(89 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 125 = true ∨ valuation q 15 = true ∨ valuation q 43 = true := by
  rw [value6, value15, value43, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(89 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (329 : Vertex) [(89 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 16 = false := by
  rw [value1, value7, value9, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (74 : Vertex) (66 : Vertex) (78 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 44 = false := by
  rw [value1, value7, value9, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (74 : Vertex) (66 : Vertex) (78 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 126 = true ∨ valuation q 9 = true ∨ valuation q 16 = true ∨ valuation q 44 = true := by
  rw [value7, value9, value16, value44, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(78 : Vertex), (90 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (66 : Vertex) [(78 : Vertex), (90 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 126 = true ∨ valuation q 1 = true ∨ valuation q 16 = true ∨ valuation q 44 = true := by
  rw [value1, value7, value16, value44, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(66 : Vertex), (90 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (78 : Vertex) [(66 : Vertex), (90 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 126 = true ∨ valuation q 1 = true ∨ valuation q 9 = true ∨ valuation q 44 = true := by
  rw [value1, value7, value9, value44, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(66 : Vertex), (78 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (90 : Vertex) [(66 : Vertex), (78 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E078.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112078
