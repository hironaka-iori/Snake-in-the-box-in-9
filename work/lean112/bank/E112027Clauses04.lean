import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 21 = true ∨ valuation q 25 = true ∨ valuation q 87 = true := by
  rw [value16, value21, value23, value25, value87, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(130 : Vertex), (136 : Vertex), (142 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (154 : Vertex) [(130 : Vertex), (136 : Vertex), (142 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 21 = true ∨ valuation q 25 = true ∨ valuation q 31 = true := by
  rw [value16, value21, value23, value25, value31, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(130 : Vertex), (136 : Vertex), (142 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (394 : Vertex) [(130 : Vertex), (136 : Vertex), (142 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 24 = true := by
  rw [value24, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (140 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 18 = true ∨ valuation q 21 = true ∨ valuation q 25 = true ∨ valuation q 88 = true := by
  rw [value18, value21, value24, value25, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ∈ [(132 : Vertex), (136 : Vertex), (142 : Vertex), (396 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (140 : Vertex) [(132 : Vertex), (136 : Vertex), (142 : Vertex), (396 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 18 = false ∨ valuation q 88 = false := by
  rw [value18, value88, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (140 : Vertex) (132 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 21 = false ∨ valuation q 88 = false := by
  rw [value21, value88, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (140 : Vertex) (136 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 25 = false ∨ valuation q 88 = false := by
  rw [value25, value88, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (140 : Vertex) (142 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 21 = true ∨ valuation q 25 = true ∨ valuation q 88 = true := by
  rw [value21, value24, value25, value88, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(136 : Vertex), (142 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (132 : Vertex) [(136 : Vertex), (142 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 18 = true ∨ valuation q 25 = true ∨ valuation q 88 = true := by
  rw [value18, value24, value25, value88, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(132 : Vertex), (142 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (136 : Vertex) [(132 : Vertex), (142 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 18 = true ∨ valuation q 21 = true ∨ valuation q 88 = true := by
  rw [value18, value21, value24, value88, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(132 : Vertex), (136 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (142 : Vertex) [(132 : Vertex), (136 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 18 = true ∨ valuation q 21 = true ∨ valuation q 25 = true := by
  rw [value18, value21, value24, value25, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(132 : Vertex), (136 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (396 : Vertex) [(132 : Vertex), (136 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value19, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 90 = false := by
  rw [value19, value23, value25, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (138 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 90 = false := by
  rw [value23, value24, value25, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (138 : Vertex) (140 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 90 = true := by
  rw [value23, value24, value25, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(138 : Vertex), (140 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (134 : Vertex) [(138 : Vertex), (140 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 19 = true ∨ valuation q 24 = true ∨ valuation q 90 = true := by
  rw [value19, value24, value25, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(134 : Vertex), (140 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (138 : Vertex) [(134 : Vertex), (140 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 19 = true ∨ valuation q 23 = true ∨ valuation q 90 = true := by
  rw [value19, value23, value25, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(134 : Vertex), (138 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (140 : Vertex) [(134 : Vertex), (138 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 15 = false ∨ valuation q 27 = false ∨ valuation q 92 = false := by
  rw [value15, value26, value27, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (128 : Vertex) (148 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 92 = true := by
  rw [value15, value26, value92, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(128 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (148 : Vertex) [(128 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 18 = true ∨ valuation q 28 = true := by
  rw [value18, value27, value28, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(132 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(132 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 18 = true ∨ valuation q 26 = true := by
  rw [value18, value26, value27, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(132 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (149 : Vertex) [(132 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 29 = true := by
  rw [value28, value29, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(151 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (148 : Vertex) [(151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 27 = true := by
  rw [value27, value28, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(148 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (151 : Vertex) [(148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 33 = false := by
  rw [value20, value28, value29, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (135 : Vertex) (149 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 20 = true ∨ valuation q 33 = true := by
  rw [value20, value29, value33, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(135 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (149 : Vertex) [(135 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 20 = true ∨ valuation q 28 = true := by
  rw [value20, value28, value29, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(135 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (159 : Vertex) [(135 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 32 = true := by
  rw [value30, value32, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(155 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (137 : Vertex) [(155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 22 = true := by
  rw [value22, value30, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(137 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (155 : Vertex) [(137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 47 = false := by
  rw [value23, value31, value32, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 97 = false := by
  rw [value23, value31, value32, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 23 = false ∨ valuation q 47 = false ∨ valuation q 97 = false := by
  rw [value23, value31, value47, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (218 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 47 = false ∨ valuation q 97 = false := by
  rw [value31, value32, value47, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (155 : Vertex) (218 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E027.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112027
