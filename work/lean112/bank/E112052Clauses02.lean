import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 38 = false := by
  rw [value20, value21, value22, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (141 : Vertex) (142 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 38 = false := by
  rw [value20, value21, value29, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (141 : Vertex) (156 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 147 = true ∨ valuation q 21 = true ∨ valuation q 22 = true ∨ valuation q 29 = true ∨ valuation q 38 = true := by
  rw [value20, value21, value22, value29, value38, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(141 : Vertex), (142 : Vertex), (156 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (132 : Vertex) [(141 : Vertex), (142 : Vertex), (156 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 147 = true ∨ valuation q 16 = true ∨ valuation q 22 = true ∨ valuation q 29 = true ∨ valuation q 38 = true := by
  rw [value16, value20, value22, value29, value38, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(132 : Vertex), (142 : Vertex), (156 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (141 : Vertex) [(132 : Vertex), (142 : Vertex), (156 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 147 = true ∨ valuation q 16 = true ∨ valuation q 21 = true ∨ valuation q 22 = true ∨ valuation q 38 = true := by
  rw [value16, value20, value21, value22, value38, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(132 : Vertex), (141 : Vertex), (142 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (156 : Vertex) [(132 : Vertex), (141 : Vertex), (142 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value17, value18, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 95 = false := by
  rw [value17, value18, value21, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 95 = false := by
  rw [value17, value20, value21, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (140 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 95 = false := by
  rw [value18, value20, value21, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (137 : Vertex) (140 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value17, value18, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 148 = true ∨ valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 95 = true := by
  rw [value18, value20, value21, value95, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(137 : Vertex), (140 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (133 : Vertex) [(137 : Vertex), (140 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 148 = true ∨ valuation q 17 = true ∨ valuation q 20 = true ∨ valuation q 95 = true := by
  rw [value17, value20, value21, value95, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(133 : Vertex), (140 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (137 : Vertex) [(133 : Vertex), (140 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 148 = true ∨ valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 95 = true := by
  rw [value17, value18, value21, value95, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(133 : Vertex), (137 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (140 : Vertex) [(133 : Vertex), (137 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 148 = true ∨ valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 20 = true := by
  rw [value17, value18, value20, value21, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(133 : Vertex), (137 : Vertex), (140 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (397 : Vertex) [(133 : Vertex), (137 : Vertex), (140 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 30 = false ∨ valuation q 39 = false := by
  rw [value20, value22, value30, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (140 : Vertex) (158 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 30 = false ∨ valuation q 96 = false := by
  rw [value20, value22, value30, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (140 : Vertex) (158 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 39 = false ∨ valuation q 96 = false := by
  rw [value20, value22, value39, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (140 : Vertex) (206 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 39 = false ∨ valuation q 96 = false := by
  rw [value22, value30, value39, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (158 : Vertex) (206 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 149 = true ∨ valuation q 20 = true ∨ valuation q 39 = true ∨ valuation q 96 = true := by
  rw [value20, value22, value39, value96, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(140 : Vertex), (206 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (158 : Vertex) [(140 : Vertex), (206 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 28 = true := by
  rw [value23, value24, value25, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ∈ [(145 : Vertex), (146 : Vertex), (152 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (144 : Vertex) [(145 : Vertex), (146 : Vertex), (152 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value23, value24, value25, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (145 : Vertex) (146 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 150 = true ∨ valuation q 25 = true ∨ valuation q 28 = true := by
  rw [value23, value25, value28, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(146 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (145 : Vertex) [(146 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 150 = true ∨ valuation q 24 = true ∨ valuation q 28 = true := by
  rw [value23, value24, value28, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(145 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (146 : Vertex) [(145 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 150 = true ∨ valuation q 24 = true ∨ valuation q 25 = true := by
  rw [value23, value24, value25, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(145 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (152 : Vertex) [(145 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 97 = false := by
  rw [value23, value24, value26, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (144 : Vertex) (147 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 26 = true ∨ valuation q 40 = true ∨ valuation q 97 = true := by
  rw [value24, value26, value40, value97, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(147 : Vertex), (209 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (144 : Vertex) [(147 : Vertex), (209 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 23 = true ∨ valuation q 26 = true ∨ valuation q 97 = true := by
  rw [value23, value24, value26, value97, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(144 : Vertex), (147 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (209 : Vertex) [(144 : Vertex), (147 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 23 = true ∨ valuation q 26 = true ∨ valuation q 40 = true := by
  rw [value23, value24, value26, value40, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(144 : Vertex), (147 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (401 : Vertex) [(144 : Vertex), (147 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 14 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value14, value23, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (144 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 23 = true ∨ valuation q 26 = true := by
  rw [value23, value25, value26, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(144 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (130 : Vertex) [(144 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 14 = true ∨ valuation q 26 = true := by
  rw [value14, value25, value26, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(130 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (144 : Vertex) [(130 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 14 = true ∨ valuation q 23 = true := by
  rw [value14, value23, value25, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(130 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (147 : Vertex) [(130 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E052.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112052
