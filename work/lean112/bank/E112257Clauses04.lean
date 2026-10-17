import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 26 = false ∨ valuation q 89 = false := by
  rw [value19, value24, value26, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (45 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 32 = false ∨ valuation q 62 = false := by
  rw [value19, value24, value32, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (57 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 32 = false ∨ valuation q 89 = false := by
  rw [value19, value24, value32, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (57 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value19, value24, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (169 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value23, value24, value26, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (45 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 62 = false := by
  rw [value23, value24, value26, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (45 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 89 = false := by
  rw [value23, value24, value26, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (45 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 62 = false := by
  rw [value23, value24, value32, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (57 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 89 = false := by
  rw [value23, value24, value32, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (57 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value23, value24, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (169 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 32 = false ∨ valuation q 62 = false := by
  rw [value24, value26, value32, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (45 : Vertex) (57 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 32 = false ∨ valuation q 89 = false := by
  rw [value24, value26, value32, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (45 : Vertex) (57 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value24, value26, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (45 : Vertex) (169 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value24, value32, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (57 : Vertex) (169 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 63 = false := by
  rw [value7, value23, value25, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (10 : Vertex) (40 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 7 = false ∨ valuation q 23 = false := by
  rw [value7, value23, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (42 : Vertex) (10 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 23 = true ∨ valuation q 63 = true := by
  rw [value23, value25, value63, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(40 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (10 : Vertex) [(40 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 7 = true ∨ valuation q 63 = true := by
  rw [value7, value25, value63, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(10 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (40 : Vertex) [(10 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value8, value24, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (45 : Vertex) (13 : Vertex) (41 : Vertex) (47 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 65 = true := by
  rw [value24, value26, value27, value65, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (45 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(41 : Vertex), (47 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (45 : Vertex) (13 : Vertex) [(41 : Vertex), (47 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 8 = true ∨ valuation q 24 = true ∨ valuation q 65 = true := by
  rw [value8, value24, value26, value65, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (45 : Vertex) w → w ∈ region → w ≠ (47 : Vertex) → w ∈ [(13 : Vertex), (41 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (45 : Vertex) (47 : Vertex) [(13 : Vertex), (41 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 8 = true ∨ valuation q 24 = true ∨ valuation q 27 = true := by
  rw [value8, value24, value26, value27, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (45 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(13 : Vertex), (41 : Vertex), (47 : Vertex)] := by decide
  have hg := other_cover q (45 : Vertex) (173 : Vertex) [(13 : Vertex), (41 : Vertex), (47 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 66 = true := by
  rw [value27, value66, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (47 : Vertex) w → w ∈ region → w ≠ (45 : Vertex) → w ∈ [(175 : Vertex)] := by decide
  have hg := other_cover q (47 : Vertex) (45 : Vertex) [(175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 26 = true := by
  rw [value26, value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (47 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(45 : Vertex)] := by decide
  have hg := other_cover q (47 : Vertex) (175 : Vertex) [(45 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 29 = true ∨ valuation q 67 = true := by
  rw [value28, value29, value67, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(50 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (16 : Vertex) [(50 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 10 = true ∨ valuation q 67 = true := by
  rw [value10, value28, value67, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(16 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (50 : Vertex) [(16 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 10 = true ∨ valuation q 29 = true := by
  rw [value10, value28, value29, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(16 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (176 : Vertex) [(16 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 29 = true := by
  rw [value29, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (50 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 68 = false := by
  rw [value12, value28, value29, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (48 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 28 = true ∨ valuation q 68 = true := by
  rw [value28, value29, value68, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(48 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (18 : Vertex) [(48 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 12 = true ∨ valuation q 68 = true := by
  rw [value12, value29, value68, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(18 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (48 : Vertex) [(18 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(55 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (21 : Vertex) [(55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E257.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112257
