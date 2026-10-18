import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 135 = true ∨ valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 32 = true := by
  rw [value22, value24, value25, value32, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(129 : Vertex), (135 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(129 : Vertex), (135 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 135 = true ∨ valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 25 = true := by
  rw [value22, value23, value24, value25, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(129 : Vertex), (130 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (147 : Vertex) [(129 : Vertex), (130 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 42 = false := by
  rw [value24, value25, value28, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 137 = true ∨ valuation q 22 = true ∨ valuation q 44 = true ∨ valuation q 83 = true := by
  rw [value22, value26, value44, value83, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(129 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (141 : Vertex) [(129 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 137 = true ∨ valuation q 22 = true ∨ valuation q 27 = true ∨ valuation q 44 = true := by
  rw [value22, value26, value27, value44, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(129 : Vertex), (141 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value26, value27, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (137 : Vertex) (143 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 139 = true ∨ valuation q 27 = true ∨ valuation q 38 = true := by
  rw [value27, value28, value38, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(141 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (135 : Vertex) [(141 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 139 = true ∨ valuation q 25 = true ∨ valuation q 38 = true := by
  rw [value25, value28, value38, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(135 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (141 : Vertex) [(135 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 139 = true ∨ valuation q 25 = true ∨ valuation q 27 = true := by
  rw [value25, value27, value28, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(135 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (159 : Vertex) [(135 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value29, value30, value31, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (145 : Vertex) (146 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 140 = true ∨ valuation q 31 = true ∨ valuation q 33 = true := by
  rw [value29, value31, value33, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(146 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (145 : Vertex) [(146 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 141 = true ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value22, value30, value32, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(129 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (144 : Vertex) [(129 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 141 = true ∨ valuation q 22 = true ∨ valuation q 29 = true := by
  rw [value22, value29, value30, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(129 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (147 : Vertex) [(129 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value24, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (145 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 143 = true ∨ valuation q 30 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value32, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(145 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (131 : Vertex) [(145 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 144 = true ∨ valuation q 35 = true := by
  rw [value33, value35, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(156 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 144 = true ∨ valuation q 29 = true := by
  rw [value29, value33, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (156 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 37 = false ∨ valuation q 53 = false := by
  rw [value31, value34, value37, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (146 : Vertex) (158 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value33, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (148 : Vertex) (157 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value35, value36, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (156 : Vertex) (221 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value36, value38, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (159 : Vertex) (221 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 38 = false := by
  rw [value34, value35, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (154 : Vertex) (156 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 148 = true ∨ valuation q 35 = true ∨ valuation q 38 = true := by
  rw [value35, value37, value38, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(156 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (154 : Vertex) [(156 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 148 = true ∨ valuation q 34 = true ∨ valuation q 38 = true := by
  rw [value34, value37, value38, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (156 : Vertex) [(154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 148 = true ∨ valuation q 34 = true ∨ valuation q 35 = true := by
  rw [value34, value35, value37, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(154 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (159 : Vertex) [(154 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 28 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value28, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (143 : Vertex) (157 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 149 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value38, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(157 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (143 : Vertex) [(157 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 150 = true ∨ valuation q 43 = true := by
  rw [value39, value43, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(200 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 150 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(193 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 39 = false := by
  rw [value4, value22, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 151 = true ∨ valuation q 22 = true ∨ valuation q 39 = true ∨ valuation q 44 = true := by
  rw [value22, value39, value40, value44, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(129 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (65 : Vertex) [(129 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 151 = true ∨ valuation q 4 = true ∨ valuation q 22 = true ∨ valuation q 44 = true := by
  rw [value4, value22, value40, value44, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(65 : Vertex), (129 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (192 : Vertex) [(65 : Vertex), (129 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E148.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112148
