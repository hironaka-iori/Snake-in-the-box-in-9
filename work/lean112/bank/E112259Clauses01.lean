import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 60 = false := by
  rw [value5, value7, value23, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (10 : Vertex) (40 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 23 = false ∨ valuation q 60 = false := by
  rw [value5, value14, value23, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (8 : Vertex) (24 : Vertex) (40 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 121 = true ∨ valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 14 = true ∨ valuation q 23 = true ∨ valuation q 60 = true := by
  rw [value5, value6, value7, value14, value23, value60, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (8 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(9 : Vertex), (10 : Vertex), (24 : Vertex), (40 : Vertex), (136 : Vertex)] := by decide
  have hg := other_cover q (8 : Vertex) (0 : Vertex) [(9 : Vertex), (10 : Vertex), (24 : Vertex), (40 : Vertex), (136 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 61 = false := by
  rw [value5, value6, value8, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (9 : Vertex) (8 : Vertex) (13 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 5 = true ∨ valuation q 61 = true := by
  rw [value5, value6, value61, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (9 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(8 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (9 : Vertex) (13 : Vertex) [(8 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 122 = true ∨ valuation q 5 = true ∨ valuation q 8 = true := by
  rw [value5, value6, value8, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (9 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(8 : Vertex), (13 : Vertex)] := by decide
  have hg := other_cover q (9 : Vertex) (137 : Vertex) [(8 : Vertex), (13 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 24 = false := by
  rw [value5, value7, value9, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (10 : Vertex) (8 : Vertex) (14 : Vertex) (42 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 9 = true ∨ valuation q 24 = true := by
  rw [value7, value9, value24, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(14 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (8 : Vertex) [(14 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 5 = true ∨ valuation q 24 = true := by
  rw [value5, value7, value24, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(8 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (14 : Vertex) [(8 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 5 = true ∨ valuation q 9 = true := by
  rw [value5, value7, value9, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (10 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(8 : Vertex), (14 : Vertex)] := by decide
  have hg := other_cover q (10 : Vertex) (42 : Vertex) [(8 : Vertex), (14 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 25 = false ∨ valuation q 63 = false := by
  rw [value6, value8, value25, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (9 : Vertex) (45 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 25 = true ∨ valuation q 63 = true := by
  rw [value8, value25, value63, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(45 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (9 : Vertex) [(45 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 63 = true := by
  rw [value6, value8, value63, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (45 : Vertex) → w ∈ [(9 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (45 : Vertex) [(9 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 124 = true ∨ valuation q 6 = true ∨ valuation q 25 = true := by
  rw [value6, value8, value25, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(9 : Vertex), (45 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (141 : Vertex) [(9 : Vertex), (45 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = true ∨ valuation q 17 = true ∨ valuation q 64 = true := by
  rw [value7, value9, value17, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ∈ [(10 : Vertex), (30 : Vertex), (142 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (14 : Vertex) [(10 : Vertex), (30 : Vertex), (142 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = false ∨ valuation q 17 = false ∨ valuation q 64 = false := by
  rw [value7, value9, value17, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (14 : Vertex) (10 : Vertex) (30 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 7 = false ∨ valuation q 64 = false := by
  rw [value7, value64, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (14 : Vertex) (10 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 17 = true ∨ valuation q 64 = true := by
  rw [value9, value17, value64, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(30 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (10 : Vertex) [(30 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 7 = true ∨ valuation q 64 = true := by
  rw [value7, value9, value64, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(10 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (30 : Vertex) [(10 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 7 = true ∨ valuation q 17 = true := by
  rw [value7, value9, value17, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(10 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (142 : Vertex) [(10 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 28 = true := by
  rw [value10, value28, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(49 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (21 : Vertex) [(49 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 12 = true := by
  rw [value10, value12, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(21 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (49 : Vertex) [(21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 29 = false ∨ valuation q 65 = false := by
  rw [value11, value13, value29, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (22 : Vertex) (50 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 29 = true ∨ valuation q 65 = true := by
  rw [value11, value29, value65, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(50 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(50 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 13 = true ∨ valuation q 65 = true := by
  rw [value11, value13, value65, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(22 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (50 : Vertex) [(22 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 13 = true ∨ valuation q 29 = true := by
  rw [value11, value13, value29, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(22 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (146 : Vertex) [(22 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = true ∨ valuation q 30 = true ∨ valuation q 68 = true := by
  rw [value10, value12, value30, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ∈ [(17 : Vertex), (53 : Vertex), (149 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (21 : Vertex) [(17 : Vertex), (53 : Vertex), (149 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 30 = false ∨ valuation q 68 = false := by
  rw [value10, value12, value30, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (53 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 30 = true ∨ valuation q 68 = true := by
  rw [value12, value30, value68, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(53 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (17 : Vertex) [(53 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 10 = true ∨ valuation q 68 = true := by
  rw [value10, value12, value68, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(17 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (53 : Vertex) [(17 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 10 = true ∨ valuation q 30 = true := by
  rw [value10, value12, value30, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(17 : Vertex), (53 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (149 : Vertex) [(17 : Vertex), (53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 17 = false ∨ valuation q 69 = false := by
  rw [value11, value13, value17, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (18 : Vertex) (30 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E259.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112259
