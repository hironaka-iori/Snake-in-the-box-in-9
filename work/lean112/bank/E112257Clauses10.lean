import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 174 = true ∨ valuation q 63 = true ∨ valuation q 68 = true := by
  rw [value58, value63, value68, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(170 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (166 : Vertex) [(170 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 57 = true ∨ valuation q 65 = true := by
  rw [value57, value59, value65, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(161 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (133 : Vertex) [(161 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 38 = true ∨ valuation q 65 = true := by
  rw [value38, value59, value65, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(133 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (161 : Vertex) [(133 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 38 = true ∨ valuation q 57 = true := by
  rw [value38, value57, value59, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(133 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (173 : Vertex) [(133 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 58 = false := by
  rw [value22, value39, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (38 : Vertex) (134 : Vertex) (162 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 39 = true ∨ valuation q 58 = true := by
  rw [value39, value58, value60, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(134 : Vertex), (162 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (38 : Vertex) [(134 : Vertex), (162 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 22 = true ∨ valuation q 58 = true := by
  rw [value22, value58, value60, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(38 : Vertex), (162 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (134 : Vertex) [(38 : Vertex), (162 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 22 = true ∨ valuation q 39 = true := by
  rw [value22, value39, value60, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(38 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (162 : Vertex) [(38 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 23 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value23, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (169 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 23 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value23, value61, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (169 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 23 = false ∨ valuation q 62 = false ∨ valuation q 72 = false := by
  rw [value23, value61, value62, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (169 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 23 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value23, value61, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (170 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 23 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value23, value61, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (172 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value61, value62, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (169 : Vertex) (170 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value61, value62, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (169 : Vertex) (170 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value61, value63, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (170 : Vertex) (172 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 23 = false ∨ valuation q 72 = false := by
  rw [value23, value72, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (168 : Vertex) (40 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 177 = true ∨ valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 64 = true ∨ valuation q 72 = true := by
  rw [value61, value62, value63, value64, value72, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(169 : Vertex), (170 : Vertex), (172 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (40 : Vertex) [(169 : Vertex), (170 : Vertex), (172 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 177 = true ∨ valuation q 23 = true ∨ valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 72 = true := by
  rw [value23, value61, value62, value64, value72, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(40 : Vertex), (169 : Vertex), (172 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (170 : Vertex) [(40 : Vertex), (169 : Vertex), (172 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 65 = false := by
  rw [value24, value57, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (161 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 24 = false ∨ valuation q 57 = false ∨ valuation q 73 = false := by
  rw [value24, value57, value62, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (161 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 24 = false ∨ valuation q 61 = false ∨ valuation q 73 = false := by
  rw [value24, value61, value62, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (168 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 24 = false ∨ valuation q 65 = false ∨ valuation q 73 = false := by
  rw [value24, value62, value65, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (173 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 73 = false := by
  rw [value57, value61, value62, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (168 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 73 = false := by
  rw [value61, value62, value65, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (173 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 178 = true ∨ valuation q 57 = true ∨ valuation q 61 = true ∨ valuation q 65 = true ∨ valuation q 73 = true := by
  rw [value57, value61, value62, value65, value73, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (169 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(161 : Vertex), (168 : Vertex), (173 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (169 : Vertex) (41 : Vertex) [(161 : Vertex), (168 : Vertex), (173 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 178 = true ∨ valuation q 24 = true ∨ valuation q 61 = true ∨ valuation q 65 = true ∨ valuation q 73 = true := by
  rw [value24, value61, value62, value65, value73, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (169 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(41 : Vertex), (168 : Vertex), (173 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (169 : Vertex) (161 : Vertex) [(41 : Vertex), (168 : Vertex), (173 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 178 = true ∨ valuation q 24 = true ∨ valuation q 57 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value24, value57, value61, value62, value65, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (169 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(41 : Vertex), (161 : Vertex), (168 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (169 : Vertex) (185 : Vertex) [(41 : Vertex), (161 : Vertex), (168 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 76 = false := by
  rw [value61, value64, value65, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (172 : Vertex) (168 : Vertex) (173 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 61 = true ∨ valuation q 65 = true ∨ valuation q 76 = true := by
  rw [value61, value64, value65, value76, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(168 : Vertex), (173 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (140 : Vertex) [(168 : Vertex), (173 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 43 = true ∨ valuation q 61 = true ∨ valuation q 76 = true := by
  rw [value43, value61, value64, value76, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(140 : Vertex), (168 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (173 : Vertex) [(140 : Vertex), (168 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 43 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value43, value61, value64, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(140 : Vertex), (168 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (188 : Vertex) [(140 : Vertex), (168 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E257.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112257
