import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 126 = true ∨ valuation q 1 = true ∨ valuation q 9 = true ∨ valuation q 16 = true := by
  rw [value1, value7, value9, value16, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(66 : Vertex), (78 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (202 : Vertex) [(66 : Vertex), (78 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 45 = false := by
  rw [value3, value8, value9, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (68 : Vertex) (78 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 127 = true ∨ valuation q 9 = true ∨ valuation q 45 = true := by
  rw [value8, value9, value45, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(78 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (68 : Vertex) [(78 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 127 = true ∨ valuation q 3 = true ∨ valuation q 45 = true := by
  rw [value3, value8, value45, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(68 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (78 : Vertex) [(68 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 127 = true ∨ valuation q 3 = true ∨ valuation q 9 = true := by
  rw [value3, value8, value9, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(68 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (204 : Vertex) [(68 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value5, value7, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (70 : Vertex) (74 : Vertex) (76 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 47 = false := by
  rw [value5, value7, value9, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (70 : Vertex) (74 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 47 = false := by
  rw [value5, value8, value9, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (70 : Vertex) (76 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 47 = false := by
  rw [value7, value8, value9, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (74 : Vertex) (76 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 128 = true ∨ valuation q 7 = true ∨ valuation q 8 = true ∨ valuation q 47 = true := by
  rw [value7, value8, value9, value47, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(74 : Vertex), (76 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (70 : Vertex) [(74 : Vertex), (76 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 128 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 47 = true := by
  rw [value5, value8, value9, value47, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(70 : Vertex), (76 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (74 : Vertex) [(70 : Vertex), (76 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 128 = true ∨ valuation q 5 = true ∨ valuation q 7 = true ∨ valuation q 47 = true := by
  rw [value5, value7, value9, value47, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(70 : Vertex), (74 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (76 : Vertex) [(70 : Vertex), (74 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 49 = true := by
  rw [value10, value11, value14, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ∈ [(84 : Vertex), (88 : Vertex), (208 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (80 : Vertex) [(84 : Vertex), (88 : Vertex), (208 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 49 = false := by
  rw [value10, value11, value14, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 129 = true ∨ valuation q 14 = true ∨ valuation q 49 = true := by
  rw [value10, value14, value49, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(88 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (84 : Vertex) [(88 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 129 = true ∨ valuation q 11 = true ∨ valuation q 49 = true := by
  rw [value10, value11, value49, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(84 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (88 : Vertex) [(84 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 129 = true ∨ valuation q 11 = true ∨ valuation q 14 = true := by
  rw [value10, value11, value14, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(84 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (208 : Vertex) [(84 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 12 = false := by
  rw [value3, value10, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 130 = true ∨ valuation q 10 = true ∨ valuation q 12 = true := by
  rw [value10, value11, value12, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(80 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (68 : Vertex) [(80 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 130 = true ∨ valuation q 3 = true ∨ valuation q 12 = true := by
  rw [value3, value11, value12, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(68 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(68 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 130 = true ∨ valuation q 3 = true ∨ valuation q 10 = true := by
  rw [value3, value10, value11, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(68 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (85 : Vertex) [(68 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 13 = false := by
  rw [value4, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (69 : Vertex) (84 : Vertex) (87 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 131 = true ∨ valuation q 11 = true ∨ valuation q 13 = true := by
  rw [value11, value12, value13, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(84 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (69 : Vertex) [(84 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 131 = true ∨ valuation q 4 = true ∨ valuation q 13 = true := by
  rw [value4, value12, value13, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(69 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (84 : Vertex) [(69 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 131 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value4, value11, value12, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (87 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 132 = true ∨ valuation q 18 = true := by
  rw [value13, value18, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (85 : Vertex) [(95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 132 = true ∨ valuation q 12 = true := by
  rw [value12, value13, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (95 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 54 = false := by
  rw [value10, value14, value15, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (80 : Vertex) (89 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 133 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 54 = true := by
  rw [value14, value15, value16, value54, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(89 : Vertex), (90 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (80 : Vertex) [(89 : Vertex), (90 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 133 = true ∨ valuation q 10 = true ∨ valuation q 16 = true ∨ valuation q 54 = true := by
  rw [value10, value14, value16, value54, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(80 : Vertex), (90 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (89 : Vertex) [(80 : Vertex), (90 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 133 = true ∨ valuation q 10 = true ∨ valuation q 15 = true ∨ valuation q 54 = true := by
  rw [value10, value14, value15, value54, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(80 : Vertex), (89 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (90 : Vertex) [(80 : Vertex), (89 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 133 = true ∨ valuation q 10 = true ∨ valuation q 15 = true ∨ valuation q 16 = true := by
  rw [value10, value14, value15, value16, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(80 : Vertex), (89 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (216 : Vertex) [(80 : Vertex), (89 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E078.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112078
