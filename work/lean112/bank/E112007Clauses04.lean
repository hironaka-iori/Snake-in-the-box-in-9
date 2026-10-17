import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 36 = true ∨ valuation q 43 = true := by
  rw [value35, value36, value43, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(199 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (206 : Vertex) [(199 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 19 = false ∨ valuation q 35 = false ∨ valuation q 44 = false := by
  rw [value19, value35, value36, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (135 : Vertex) (198 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 154 = true ∨ valuation q 35 = true ∨ valuation q 44 = true := by
  rw [value35, value36, value44, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(198 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (135 : Vertex) [(198 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 10 = false ∨ valuation q 33 = false ∨ valuation q 39 = false := by
  rw [value10, value33, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 10 = false ∨ valuation q 33 = false ∨ valuation q 45 = false := by
  rw [value10, value33, value37, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 10 = false ∨ valuation q 39 = false ∨ valuation q 45 = false := by
  rw [value10, value37, value39, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 39 = false ∨ valuation q 45 = false := by
  rw [value33, value37, value39, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 45 = false := by
  rw [value37, value38, value39, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (201 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 10 = true ∨ valuation q 33 = true ∨ valuation q 38 = true ∨ valuation q 45 = true := by
  rw [value10, value33, value37, value38, value45, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(72 : Vertex), (192 : Vertex), (201 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (204 : Vertex) [(72 : Vertex), (192 : Vertex), (201 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 20 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value20, value34, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 20 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value20, value37, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value34, value37, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 105 = false := by
  rw [value34, value37, value38, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 105 = false := by
  rw [value37, value38, value46, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (217 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(206 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (200 : Vertex) [(206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 37 = true := by
  rw [value37, value39, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(200 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (206 : Vertex) [(200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 39 = true := by
  rw [value39, value40, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(204 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (198 : Vertex) [(204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 35 = true := by
  rw [value35, value40, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(198 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (204 : Vertex) [(198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 12 = false ∨ valuation q 26 = false ∨ valuation q 43 = false := by
  rw [value12, value26, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (146 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 12 = false ∨ valuation q 26 = false ∨ valuation q 47 = false := by
  rw [value12, value26, value41, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (146 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 12 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value12, value41, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 12 = true ∨ valuation q 26 = true ∨ valuation q 43 = true := by
  rw [value12, value26, value41, value43, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(82 : Vertex), (146 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (218 : Vertex) [(82 : Vertex), (146 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 49 = true := by
  rw [value42, value49, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (215 : Vertex) [(221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 44 = true := by
  rw [value42, value44, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(215 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (221 : Vertex) [(215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value35, value41, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (198 : Vertex) (210 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 114 = false := by
  rw [value35, value43, value44, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (198 : Vertex) (215 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value36, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value42, value43, value44, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(213 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (199 : Vertex) [(213 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 36 = true ∨ valuation q 43 = true := by
  rw [value36, value43, value44, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(199 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (213 : Vertex) [(199 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value37, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 115 = false := by
  rw [value37, value45, value46, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (217 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 47 = false ∨ valuation q 115 = false := by
  rw [value37, value45, value47, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E007.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112007
