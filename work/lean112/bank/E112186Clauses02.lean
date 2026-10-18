import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value14, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (144 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value14, value21, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (144 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 14 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value14, value22, value23, value24, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(132 : Vertex), (149 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(132 : Vertex), (149 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 14 = true ∨ valuation q 21 = true ∨ valuation q 23 = true := by
  rw [value14, value21, value22, value23, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(132 : Vertex), (144 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (150 : Vertex) [(132 : Vertex), (144 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value15, value22, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (133 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 42 = false := by
  rw [value22, value24, value25, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (148 : Vertex) (151 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 98 = false := by
  rw [value22, value24, value25, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (148 : Vertex) (151 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 29 = false := by
  rw [value23, value24, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (149 : Vertex) (150 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 24 = true ∨ valuation q 29 = true := by
  rw [value24, value25, value29, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(150 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (149 : Vertex) [(150 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 23 = true ∨ valuation q 29 = true := by
  rw [value23, value25, value29, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(149 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (150 : Vertex) [(149 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value23, value24, value25, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(149 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (159 : Vertex) [(149 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 27 = true ∨ valuation q 99 = true := by
  rw [value26, value27, value99, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(153 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (144 : Vertex) [(153 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 21 = true ∨ valuation q 99 = true := by
  rw [value21, value26, value99, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(144 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (153 : Vertex) [(144 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 21 = true ∨ valuation q 27 = true := by
  rw [value21, value26, value27, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(144 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (408 : Vertex) [(144 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 16 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value16, value26, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (152 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 16 = false ∨ valuation q 26 = false ∨ valuation q 100 = false := by
  rw [value16, value26, value27, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (152 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 16 = false ∨ valuation q 28 = false ∨ valuation q 100 = false := by
  rw [value16, value27, value28, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (155 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 100 = false := by
  rw [value26, value27, value28, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (152 : Vertex) (155 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 16 = true ∨ valuation q 28 = true ∨ valuation q 100 = true := by
  rw [value16, value27, value28, value100, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(137 : Vertex), (155 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (152 : Vertex) [(137 : Vertex), (155 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value18, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (139 : Vertex) (153 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 152 = true ∨ valuation q 18 = true ∨ valuation q 29 = true := by
  rw [value18, value28, value29, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(139 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (153 : Vertex) [(139 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 152 = true ∨ valuation q 18 = true ∨ valuation q 27 = true := by
  rw [value18, value27, value28, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(139 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (159 : Vertex) [(139 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value25, value28, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (159 : Vertex) (151 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 28 = true := by
  rw [value28, value29, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(155 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (151 : Vertex) [(155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 105 = false := by
  rw [value30, value31, value34, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 39 = false := by
  rw [value30, value31, value32, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (192 : Vertex) (197 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value31, value32, value35, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (197 : Vertex) (201 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 30 = true ∨ valuation q 32 = true ∨ valuation q 35 = true := by
  rw [value30, value31, value32, value35, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(192 : Vertex), (197 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (209 : Vertex) [(192 : Vertex), (197 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 31 = false := by
  rw [value1, value15, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (133 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 33 = false := by
  rw [value1, value15, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (133 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 37 = false := by
  rw [value1, value15, value32, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (133 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 1 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value1, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (193 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E186.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112186
