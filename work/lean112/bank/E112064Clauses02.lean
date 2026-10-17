import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 5 = false ∨ valuation q 15 = false := by
  rw [value5, value15, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (89 : Vertex) (73 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 131 = true ∨ valuation q 13 = true ∨ valuation q 15 = true ∨ valuation q 81 = true := by
  rw [value13, value14, value15, value81, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(88 : Vertex), (93 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (73 : Vertex) [(88 : Vertex), (93 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 84 = false := by
  rw [value11, value14, value15, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (93 : Vertex) (85 : Vertex) (89 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 132 = true ∨ valuation q 14 = true ∨ valuation q 84 = true := by
  rw [value14, value15, value84, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(89 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (85 : Vertex) [(89 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 132 = true ∨ valuation q 11 = true ∨ valuation q 84 = true := by
  rw [value11, value15, value84, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(85 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (89 : Vertex) [(85 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 132 = true ∨ valuation q 11 = true ∨ valuation q 14 = true := by
  rw [value11, value14, value15, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(85 : Vertex), (89 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (349 : Vertex) [(85 : Vertex), (89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 8 = false ∨ valuation q 45 = false ∨ valuation q 85 = false := by
  rw [value8, value16, value45, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (78 : Vertex) (222 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 133 = true ∨ valuation q 45 = true ∨ valuation q 85 = true := by
  rw [value16, value45, value85, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(222 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (78 : Vertex) [(222 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 133 = true ∨ valuation q 8 = true ∨ valuation q 85 = true := by
  rw [value8, value16, value85, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(78 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (222 : Vertex) [(78 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 133 = true ∨ valuation q 8 = true ∨ valuation q 45 = true := by
  rw [value8, value16, value45, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(78 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (350 : Vertex) [(78 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 134 = true ∨ valuation q 30 = true := by
  rw [value17, value30, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(194 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (134 : Vertex) [(194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 134 = true ∨ valuation q 20 = true := by
  rw [value17, value20, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(134 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (194 : Vertex) [(134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 135 = true ∨ valuation q 20 = true := by
  rw [value18, value20, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(134 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (133 : Vertex) [(134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 135 = true ∨ valuation q 19 = true := by
  rw [value18, value19, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(133 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (134 : Vertex) [(133 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value18, value19, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (149 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 136 = true ∨ valuation q 23 = true ∨ valuation q 32 = true := by
  rw [value19, value23, value32, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(149 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (132 : Vertex) [(149 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 136 = true ∨ valuation q 18 = true ∨ valuation q 32 = true := by
  rw [value18, value19, value32, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(132 : Vertex), (197 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (149 : Vertex) [(132 : Vertex), (197 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value17, value18, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (132 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 137 = true ∨ valuation q 18 = true ∨ valuation q 21 = true := by
  rw [value18, value20, value21, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(132 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (130 : Vertex) [(132 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 137 = true ∨ valuation q 17 = true ∨ valuation q 21 = true := by
  rw [value17, value20, value21, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(130 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (132 : Vertex) [(130 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 137 = true ∨ valuation q 17 = true ∨ valuation q 18 = true := by
  rw [value17, value18, value20, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(130 : Vertex), (132 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (142 : Vertex) [(130 : Vertex), (132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 138 = true ∨ valuation q 25 = true := by
  rw [value21, value25, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(158 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (134 : Vertex) [(158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 138 = true ∨ valuation q 20 = true := by
  rw [value20, value21, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(134 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (158 : Vertex) [(134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 139 = true ∨ valuation q 38 = true := by
  rw [value22, value38, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(209 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (149 : Vertex) [(209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 139 = true ∨ valuation q 23 = true := by
  rw [value22, value23, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(149 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (209 : Vertex) [(149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 23 = true := by
  rw [value23, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (149 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = true ∨ valuation q 22 = true ∨ valuation q 24 = true := by
  rw [value19, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ∈ [(133 : Vertex), (145 : Vertex), (151 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (149 : Vertex) [(133 : Vertex), (145 : Vertex), (151 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 19 = false ∨ valuation q 22 = false := by
  rw [value19, value22, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (149 : Vertex) (133 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 140 = true ∨ valuation q 22 = true ∨ valuation q 24 = true := by
  rw [value22, value23, value24, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(145 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (133 : Vertex) [(145 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 140 = true ∨ valuation q 19 = true ∨ valuation q 24 = true := by
  rw [value19, value23, value24, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(133 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (145 : Vertex) [(133 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true := by
  rw [value24, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (151 : Vertex) (149 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 45 = false := by
  rw [value21, value25, value28, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (142 : Vertex) (190 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E064.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112064
