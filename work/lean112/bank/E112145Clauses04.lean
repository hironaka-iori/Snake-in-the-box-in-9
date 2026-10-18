import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 159 = true ∨ valuation q 54 = true ∨ valuation q 56 = true := by
  rw [value54, value55, value56, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(201 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (221 : Vertex) [(201 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 160 = true := by
  rw [value56, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 161 = true ∨ valuation q 61 = true := by
  rw [value57, value61, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (198 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 161 = true ∨ valuation q 52 = true := by
  rw [value52, value57, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(198 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 162 = true ∨ valuation q 61 = true := by
  rw [value58, value61, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value57, value58, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 166 = true := by
  rw [value62, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (226 : Vertex) (230 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 24 = false ∨ valuation q 53 = false ∨ valuation q 65 = false := by
  rw [value24, value53, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (200 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 24 = false ∨ valuation q 53 = false ∨ valuation q 93 = false := by
  rw [value24, value53, value64, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (200 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 24 = false ∨ valuation q 65 = false ∨ valuation q 93 = false := by
  rw [value24, value64, value65, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 53 = false ∨ valuation q 65 = false ∨ valuation q 93 = false := by
  rw [value53, value64, value65, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (200 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 169 = true ∨ valuation q 64 = true := by
  rw [value64, value65, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(232 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (238 : Vertex) [(232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 1 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value1, value67, value68, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (256 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (258 : Vertex), (264 : Vertex), (384 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (256 : Vertex) [(0 : Vertex), (258 : Vertex), (264 : Vertex), (384 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 171 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value67, value68, value70, value73, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (256 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(258 : Vertex), (264 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (256 : Vertex) (0 : Vertex) [(258 : Vertex), (264 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 171 = true ∨ valuation q 1 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value1, value67, value70, value73, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (256 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(0 : Vertex), (264 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (256 : Vertex) (258 : Vertex) [(0 : Vertex), (264 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 172 = true ∨ valuation q 69 = true := by
  rw [value68, value69, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (256 : Vertex) → w ∈ [(262 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (256 : Vertex) [(262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 3 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value3, value68, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value68, value69, value72, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (270 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 67 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value67, value70, value71, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (268 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 174 = true ∨ valuation q 67 = true ∨ valuation q 71 = true := by
  rw [value67, value70, value71, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(256 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (392 : Vertex) [(256 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 71 = true := by
  rw [value71, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (268 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = true ∨ valuation q 72 = true := by
  rw [value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ∈ [(264 : Vertex), (270 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (268 : Vertex) [(264 : Vertex), (270 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 175 = true ∨ valuation q 72 = true := by
  rw [value71, value72, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(270 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (264 : Vertex) [(270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 175 = true ∨ valuation q 70 = true := by
  rw [value70, value71, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(264 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 176 = true ∨ valuation q 69 = true := by
  rw [value69, value72, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(262 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (268 : Vertex) [(262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 35 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value35, value73, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 67 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value67, value73, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (256 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 180 = true ∨ valuation q 75 = true ∨ valuation q 80 = true := by
  rw [value75, value76, value80, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 180 = true ∨ valuation q 39 = true ∨ valuation q 75 = true := by
  rw [value39, value75, value76, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(135 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (399 : Vertex) [(135 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 181 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 78 = true := by
  rw [value70, value73, value77, value78, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(264 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (136 : Vertex) [(264 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 181 = true ∨ valuation q 40 = true ∨ valuation q 73 = true ∨ valuation q 78 = true := by
  rw [value40, value73, value77, value78, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(136 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (264 : Vertex) [(136 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 181 = true ∨ valuation q 40 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value40, value70, value73, value77, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(136 : Vertex), (264 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (393 : Vertex) [(136 : Vertex), (264 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E145.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112145
