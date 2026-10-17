import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 181 = true ∨ valuation q 66 = true ∨ valuation q 69 = true ∨ valuation q 88 = true := by
  rw [value65, value66, value69, value88, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(147 : Vertex), (150 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (18 : Vertex) [(147 : Vertex), (150 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 56 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value56, value65, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (146 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 65 = true ∨ valuation q 71 = true := by
  rw [value65, value66, value71, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(146 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (131 : Vertex) [(146 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 56 = true ∨ valuation q 71 = true := by
  rw [value56, value66, value71, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(131 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (146 : Vertex) [(131 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 56 = true ∨ valuation q 65 = true := by
  rw [value56, value65, value66, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(131 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (155 : Vertex) [(131 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 57 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value57, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (149 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 57 = false ∨ valuation q 68 = false ∨ valuation q 89 = false := by
  rw [value57, value67, value68, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (149 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 89 = false := by
  rw [value57, value67, value69, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (150 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 89 = false := by
  rw [value67, value68, value69, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (149 : Vertex) (150 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 183 = true ∨ valuation q 57 = true ∨ valuation q 68 = true ∨ valuation q 69 = true := by
  rw [value57, value67, value68, value69, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(132 : Vertex), (149 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (180 : Vertex) [(132 : Vertex), (149 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 12 = false ∨ valuation q 58 = false ∨ valuation q 72 = false := by
  rw [value12, value58, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (133 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 12 = false ∨ valuation q 58 = false ∨ valuation q 90 = false := by
  rw [value12, value58, value68, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (133 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 12 = false ∨ valuation q 67 = false ∨ valuation q 72 = false := by
  rw [value12, value67, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (148 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 12 = false ∨ valuation q 67 = false ∨ valuation q 90 = false := by
  rw [value12, value67, value68, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (148 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 12 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value12, value68, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (21 : Vertex) (157 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 58 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value58, value68, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (133 : Vertex) (157 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 184 = true ∨ valuation q 58 = true ∨ valuation q 67 = true ∨ valuation q 72 = true ∨ valuation q 90 = true := by
  rw [value58, value67, value68, value72, value90, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(133 : Vertex), (148 : Vertex), (157 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (21 : Vertex) [(133 : Vertex), (148 : Vertex), (157 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 184 = true ∨ valuation q 12 = true ∨ valuation q 58 = true ∨ valuation q 67 = true ∨ valuation q 90 = true := by
  rw [value12, value58, value67, value68, value90, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(21 : Vertex), (133 : Vertex), (148 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (157 : Vertex) [(21 : Vertex), (133 : Vertex), (148 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 13 = false ∨ valuation q 59 = false ∨ valuation q 65 = false := by
  rw [value13, value59, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 13 = false ∨ valuation q 59 = false ∨ valuation q 67 = false := by
  rw [value13, value59, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 13 = false ∨ valuation q 59 = false ∨ valuation q 73 = false := by
  rw [value13, value59, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 13 = false ∨ valuation q 59 = false ∨ valuation q 100 = false := by
  rw [value13, value59, value69, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (134 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 13 = false ∨ valuation q 65 = false ∨ valuation q 73 = false := by
  rw [value13, value65, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (146 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 13 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value13, value67, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (148 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 13 = false ∨ valuation q 73 = false ∨ valuation q 100 = false := by
  rw [value13, value69, value73, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (22 : Vertex) (158 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 185 = true ∨ valuation q 13 = true ∨ valuation q 59 = true ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 100 = true := by
  rw [value13, value59, value67, value69, value73, value100, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(22 : Vertex), (134 : Vertex), (148 : Vertex), (158 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (146 : Vertex) [(22 : Vertex), (134 : Vertex), (148 : Vertex), (158 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 70 = true := by
  rw [value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (152 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 14 = true ∨ valuation q 60 = true := by
  rw [value14, value60, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ∈ [(24 : Vertex), (136 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (152 : Vertex) [(24 : Vertex), (136 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 14 = false ∨ valuation q 60 = false := by
  rw [value14, value60, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (152 : Vertex) (24 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 186 = true ∨ valuation q 60 = true := by
  rw [value60, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(136 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (24 : Vertex) [(136 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 186 = true ∨ valuation q 14 = true := by
  rw [value14, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(24 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (136 : Vertex) [(24 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 15 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value15, value62, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E259.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112259
