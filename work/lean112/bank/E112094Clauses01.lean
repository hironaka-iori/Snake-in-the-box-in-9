import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 133 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value27, value29, value30, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(136 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (130 : Vertex) [(136 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 133 = true ∨ valuation q 23 = true ∨ valuation q 30 = true := by
  rw [value23, value29, value30, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(130 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (136 : Vertex) [(130 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 133 = true ∨ valuation q 23 = true ∨ valuation q 27 = true := by
  rw [value23, value27, value29, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(130 : Vertex), (136 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (142 : Vertex) [(130 : Vertex), (136 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 25 = false ∨ valuation q 29 = false ∨ valuation q 78 = false := by
  rw [value25, value29, value30, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (138 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 134 = true ∨ valuation q 29 = true ∨ valuation q 78 = true := by
  rw [value29, value30, value78, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(138 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (134 : Vertex) [(138 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 134 = true ∨ valuation q 25 = true ∨ valuation q 78 = true := by
  rw [value25, value30, value78, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(134 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (138 : Vertex) [(134 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 134 = true ∨ valuation q 25 = true ∨ valuation q 29 = true := by
  rw [value25, value29, value30, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(134 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (398 : Vertex) [(134 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 1 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value1, value23, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (130 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 1 = false ∨ valuation q 32 = false ∨ valuation q 81 = false := by
  rw [value1, value31, value32, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (147 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 81 = false := by
  rw [value23, value31, value32, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (147 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 135 = true ∨ valuation q 1 = true ∨ valuation q 23 = true ∨ valuation q 81 = true := by
  rw [value1, value23, value31, value81, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(18 : Vertex), (130 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (147 : Vertex) [(18 : Vertex), (130 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 135 = true ∨ valuation q 1 = true ∨ valuation q 23 = true ∨ valuation q 32 = true := by
  rw [value1, value23, value31, value32, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(18 : Vertex), (130 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (402 : Vertex) [(18 : Vertex), (130 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 82 = false := by
  rw [value31, value32, value36, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (146 : Vertex) (155 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 31 = false ∨ valuation q 36 = false := by
  rw [value31, value36, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (147 : Vertex) (146 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 36 = false ∨ valuation q 82 = false := by
  rw [value36, value82, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (147 : Vertex) (155 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 136 = true ∨ valuation q 31 = true ∨ valuation q 82 = true := by
  rw [value31, value32, value82, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(146 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (155 : Vertex) [(146 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 137 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 83 = true := by
  rw [value33, value34, value37, value83, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (20 : Vertex) → w ∈ [(149 : Vertex), (156 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (20 : Vertex) [(149 : Vertex), (156 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 137 = true ∨ valuation q 2 = true ∨ valuation q 37 = true ∨ valuation q 83 = true := by
  rw [value2, value33, value37, value83, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(20 : Vertex), (156 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (149 : Vertex) [(20 : Vertex), (156 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 24 = false ∨ valuation q 33 = false ∨ valuation q 38 = false := by
  rw [value24, value33, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (133 : Vertex) (148 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 28 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value28, value35, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (155 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 140 = true ∨ valuation q 35 = true := by
  rw [value35, value36, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(153 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (147 : Vertex) [(153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 140 = true ∨ valuation q 32 = true := by
  rw [value32, value36, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(147 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (153 : Vertex) [(147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 6 = false ∨ valuation q 33 = false ∨ valuation q 38 = false := by
  rw [value6, value33, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (28 : Vertex) (148 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 38 = false ∨ valuation q 87 = false := by
  rw [value33, value37, value38, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (148 : Vertex) (157 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value34, value35, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (153 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 88 = false := by
  rw [value34, value35, value38, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (153 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 88 = false := by
  rw [value35, value37, value38, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (153 : Vertex) (156 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 142 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 88 = true := by
  rw [value34, value37, value38, value88, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(149 : Vertex), (156 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (153 : Vertex) [(149 : Vertex), (156 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value39, value41, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (230 : Vertex) (234 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 144 = true ∨ valuation q 50 = true := by
  rw [value40, value50, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (231 : Vertex) [(245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 148 = true ∨ valuation q 51 = true := by
  rw [value44, value51, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(249 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (232 : Vertex) [(249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 151 = true ∨ valuation q 39 = true ∨ valuation q 100 = true := by
  rw [value39, value47, value100, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(226 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (243 : Vertex) [(226 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E094.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112094
