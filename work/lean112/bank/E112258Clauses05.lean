import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 37 = false := by
  rw [value25, value27, value28, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (295 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 86 = false := by
  rw [value25, value27, value28, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (295 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 25 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value25, value27, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (302 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 25 = false ∨ valuation q 33 = false ∨ valuation q 86 = false := by
  rw [value25, value27, value33, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (302 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 25 = false ∨ valuation q 37 = false ∨ valuation q 86 = false := by
  rw [value25, value27, value37, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (290 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value27, value28, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (295 : Vertex) (302 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 86 = false := by
  rw [value27, value28, value33, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (295 : Vertex) (302 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 37 = false ∨ valuation q 86 = false := by
  rw [value27, value28, value37, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (295 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 86 = false := by
  rw [value27, value33, value37, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (302 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value33, value37, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (294 : Vertex) (302 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 150 = true ∨ valuation q 26 = true ∨ valuation q 27 = true := by
  rw [value26, value27, value28, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(293 : Vertex), (294 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (263 : Vertex) [(293 : Vertex), (294 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 150 = true ∨ valuation q 9 = true ∨ valuation q 27 = true := by
  rw [value9, value27, value28, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(263 : Vertex), (294 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (293 : Vertex) [(263 : Vertex), (294 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 150 = true ∨ valuation q 9 = true ∨ valuation q 26 = true := by
  rw [value9, value26, value28, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(263 : Vertex), (293 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (294 : Vertex) [(263 : Vertex), (293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 10 = false ∨ valuation q 24 = false ∨ valuation q 38 = false := by
  rw [value10, value24, value29, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (264 : Vertex) (288 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 10 = false ∨ valuation q 30 = false ∨ valuation q 38 = false := by
  rw [value10, value29, value30, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (264 : Vertex) (297 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 10 = false ∨ valuation q 38 = false ∨ valuation q 87 = false := by
  rw [value10, value29, value38, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (264 : Vertex) (312 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value24, value29, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (297 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 38 = false := by
  rw [value24, value29, value30, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (297 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 38 = false := by
  rw [value24, value29, value32, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (300 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 87 = false := by
  rw [value24, value29, value32, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (300 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 38 = false := by
  rw [value29, value30, value32, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (297 : Vertex) (300 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 87 = false := by
  rw [value29, value30, value32, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (297 : Vertex) (300 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 38 = false ∨ valuation q 87 = false := by
  rw [value29, value30, value38, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (297 : Vertex) (312 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 38 = false ∨ valuation q 87 = false := by
  rw [value29, value32, value38, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (300 : Vertex) (312 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 88 = false := by
  rw [value29, value30, value31, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (296 : Vertex) (299 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value29, value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (297 : Vertex) (296 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 31 = false ∨ valuation q 88 = false := by
  rw [value31, value88, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (297 : Vertex) (299 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 152 = true ∨ valuation q 29 = true ∨ valuation q 88 = true := by
  rw [value29, value30, value88, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(296 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (299 : Vertex) [(296 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 152 = true ∨ valuation q 29 = true ∨ valuation q 31 = true := by
  rw [value29, value30, value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(296 : Vertex), (299 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (425 : Vertex) [(296 : Vertex), (299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 30 = true ∨ valuation q 89 = true := by
  rw [value30, value31, value89, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(297 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (267 : Vertex) [(297 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 11 = true ∨ valuation q 89 = true := by
  rw [value11, value31, value89, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(267 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (297 : Vertex) [(267 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 11 = true ∨ valuation q 30 = true := by
  rw [value11, value30, value31, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(267 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (427 : Vertex) [(267 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E258.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112258
