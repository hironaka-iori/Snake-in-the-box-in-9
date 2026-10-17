import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 14 = false := by
  rw [value3, value10, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (16 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value3, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (2 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value10, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (16 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 13 = true := by
  rw [value13, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (19 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = true ∨ valuation q 11 = true ∨ valuation q 12 = true := by
  rw [value4, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ∈ [(3 : Vertex), (17 : Vertex), (18 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (19 : Vertex) [(3 : Vertex), (17 : Vertex), (18 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 123 = true ∨ valuation q 4 = true ∨ valuation q 12 = true := by
  rw [value4, value12, value13, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(3 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (17 : Vertex) [(3 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 123 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value4, value11, value13, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(3 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (18 : Vertex) [(3 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 6 = true ∨ valuation q 12 = true ∨ valuation q 18 = true := by
  rw [value6, value12, value14, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ∈ [(6 : Vertex), (18 : Vertex), (30 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (22 : Vertex) [(6 : Vertex), (18 : Vertex), (30 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 124 = true ∨ valuation q 12 = true ∨ valuation q 18 = true := by
  rw [value12, value14, value18, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(18 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(18 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 18 = true := by
  rw [value6, value14, value18, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(6 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(6 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 12 = true := by
  rw [value6, value12, value14, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(6 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (30 : Vertex) [(6 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 10 = false ∨ valuation q 16 = false ∨ valuation q 32 = false := by
  rw [value10, value15, value16, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (24 : Vertex) (16 : Vertex) (28 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 17 = true ∨ valuation q 18 = true := by
  rw [value16, value17, value18, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(29 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (24 : Vertex) [(29 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value15, value16, value18, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(24 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (29 : Vertex) [(24 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 15 = true ∨ valuation q 17 = true := by
  rw [value15, value16, value17, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(24 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(24 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 8 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value8, value16, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (13 : Vertex) (28 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 127 = true ∨ valuation q 8 = true ∨ valuation q 16 = true := by
  rw [value8, value16, value17, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(13 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (31 : Vertex) [(13 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value14, value16, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (30 : Vertex) (22 : Vertex) (28 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 36 = false ∨ valuation q 77 = false := by
  rw [value9, value19, value36, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (95 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 129 = true ∨ valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 36 = true ∨ valuation q 77 = true := by
  rw [value17, value18, value19, value36, value77, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(29 : Vertex), (30 : Vertex), (95 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (15 : Vertex) [(29 : Vertex), (30 : Vertex), (95 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 3 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value3, value20, value21, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (2 : Vertex) (67 : Vertex) (74 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 130 = true ∨ valuation q 3 = true ∨ valuation q 21 = true := by
  rw [value3, value20, value21, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(2 : Vertex), (67 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (74 : Vertex) [(2 : Vertex), (67 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 20 = false ∨ valuation q 53 = false := by
  rw [value4, value20, value21, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (3 : Vertex) (66 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 131 = true ∨ valuation q 4 = true ∨ valuation q 25 = true ∨ valuation q 53 = true := by
  rw [value4, value21, value25, value53, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(3 : Vertex), (75 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (66 : Vertex) [(3 : Vertex), (75 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 131 = true ∨ valuation q 4 = true ∨ valuation q 20 = true ∨ valuation q 25 = true := by
  rw [value4, value20, value21, value25, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(3 : Vertex), (66 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (195 : Vertex) [(3 : Vertex), (66 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 29 = false := by
  rw [value22, value23, value26, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (69 : Vertex) (76 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 132 = true ∨ valuation q 23 = true ∨ valuation q 29 = true := by
  rw [value22, value23, value29, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (76 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 132 = true ∨ valuation q 23 = true ∨ valuation q 26 = true := by
  rw [value22, value23, value26, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(69 : Vertex), (76 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(69 : Vertex), (76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 5 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value5, value22, value23, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (68 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 133 = true ∨ valuation q 22 = true ∨ valuation q 30 = true := by
  rw [value22, value23, value30, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(68 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (5 : Vertex) [(68 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 133 = true ∨ valuation q 5 = true ∨ valuation q 30 = true := by
  rw [value5, value23, value30, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(5 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (68 : Vertex) [(5 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 133 = true ∨ valuation q 5 = true ∨ valuation q 22 = true := by
  rw [value5, value22, value23, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(5 : Vertex), (68 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (85 : Vertex) [(5 : Vertex), (68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E183.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112183
