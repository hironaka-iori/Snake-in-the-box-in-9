import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 41 = false := by
  rw [value15, value22, value23, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (285 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 81 = false := by
  rw [value15, value22, value23, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (285 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 41 = false ∨ valuation q 81 = false := by
  rw [value15, value23, value41, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (319 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 41 = false := by
  rw [value19, value22, value23, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (285 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 81 = false := by
  rw [value19, value22, value23, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (285 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 41 = false ∨ valuation q 81 = false := by
  rw [value19, value23, value41, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (319 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 41 = false ∨ valuation q 81 = false := by
  rw [value22, value23, value41, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (285 : Vertex) (319 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 145 = true ∨ valuation q 15 = true ∨ valuation q 22 = true ∨ valuation q 41 = true ∨ valuation q 81 = true := by
  rw [value15, value22, value23, value41, value81, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(271 : Vertex), (285 : Vertex), (319 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(271 : Vertex), (285 : Vertex), (319 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 145 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 41 = true ∨ valuation q 81 = true := by
  rw [value15, value19, value23, value41, value81, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (285 : Vertex) → w ∈ [(271 : Vertex), (279 : Vertex), (319 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (285 : Vertex) [(271 : Vertex), (279 : Vertex), (319 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 145 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 22 = true ∨ valuation q 81 = true := by
  rw [value15, value19, value22, value23, value81, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (319 : Vertex) → w ∈ [(271 : Vertex), (279 : Vertex), (285 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (319 : Vertex) [(271 : Vertex), (279 : Vertex), (285 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 145 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 22 = true ∨ valuation q 41 = true := by
  rw [value15, value19, value22, value23, value41, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(271 : Vertex), (279 : Vertex), (285 : Vertex), (319 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (415 : Vertex) [(271 : Vertex), (279 : Vertex), (285 : Vertex), (319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 32 = false ∨ valuation q 82 = false := by
  rw [value24, value25, value32, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (290 : Vertex) (304 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 25 = false ∨ valuation q 82 = false := by
  rw [value25, value82, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (288 : Vertex) (290 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 146 = true ∨ valuation q 32 = true ∨ valuation q 82 = true := by
  rw [value24, value32, value82, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (290 : Vertex) → w ∈ [(304 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (290 : Vertex) [(304 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 147 = true ∨ valuation q 24 = true := by
  rw [value24, value25, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (290 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(288 : Vertex)] := by decide
  have hg := other_cover q (290 : Vertex) (258 : Vertex) [(288 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 147 = true ∨ valuation q 7 = true := by
  rw [value7, value25, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (290 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(258 : Vertex)] := by decide
  have hg := other_cover q (290 : Vertex) (288 : Vertex) [(258 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = true ∨ valuation q 27 = true := by
  rw [value8, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ∈ [(261 : Vertex), (295 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (293 : Vertex) [(261 : Vertex), (295 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 8 = false ∨ valuation q 27 = false := by
  rw [value8, value27, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (293 : Vertex) (261 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 148 = true ∨ valuation q 27 = true := by
  rw [value26, value27, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(295 : Vertex)] := by decide
  have hg := other_cover q (293 : Vertex) (261 : Vertex) [(295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 148 = true ∨ valuation q 8 = true := by
  rw [value8, value26, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(261 : Vertex)] := by decide
  have hg := other_cover q (293 : Vertex) (295 : Vertex) [(261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 149 = true ∨ valuation q 26 = true ∨ valuation q 85 = true := by
  rw [value26, value27, value85, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(293 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (263 : Vertex) [(293 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 149 = true ∨ valuation q 10 = true ∨ valuation q 85 = true := by
  rw [value10, value27, value85, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(263 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (293 : Vertex) [(263 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 149 = true ∨ valuation q 10 = true ∨ valuation q 26 = true := by
  rw [value10, value26, value27, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(263 : Vertex), (293 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (423 : Vertex) [(263 : Vertex), (293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 28 = true := by
  rw [value28, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (297 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 29 = false ∨ valuation q 86 = false := by
  rw [value29, value86, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (297 : Vertex) (299 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 150 = true ∨ valuation q 12 = true ∨ valuation q 86 = true := by
  rw [value12, value28, value86, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(265 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (299 : Vertex) [(265 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 150 = true ∨ valuation q 12 = true ∨ valuation q 29 = true := by
  rw [value12, value28, value29, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(265 : Vertex), (299 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (425 : Vertex) [(265 : Vertex), (299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 28 = false ∨ valuation q 88 = false := by
  rw [value13, value28, value29, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (299 : Vertex) (267 : Vertex) (297 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 151 = true ∨ valuation q 28 = true ∨ valuation q 88 = true := by
  rw [value28, value29, value88, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(297 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (267 : Vertex) [(297 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 151 = true ∨ valuation q 13 = true ∨ valuation q 88 = true := by
  rw [value13, value29, value88, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(267 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (297 : Vertex) [(267 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 151 = true ∨ valuation q 13 = true ∨ valuation q 28 = true := by
  rw [value13, value28, value29, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(267 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (427 : Vertex) [(267 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 14 = false ∨ valuation q 31 = false := by
  rw [value14, value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (300 : Vertex) (268 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E254.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112254
