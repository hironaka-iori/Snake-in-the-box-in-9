import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 19 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value19, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (27 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value48, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (147 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value52, value55, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (155 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 170 = true ∨ valuation q 19 = true ∨ valuation q 52 = true ∨ valuation q 55 = true := by
  rw [value19, value52, value53, value55, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(27 : Vertex), (154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (147 : Vertex) [(27 : Vertex), (154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 170 = true ∨ valuation q 19 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value19, value48, value52, value53, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(27 : Vertex), (147 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (159 : Vertex) [(27 : Vertex), (147 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 54 = true := by
  rw [value54, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (157 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 21 = true ∨ valuation q 50 = true ∨ valuation q 55 = true := by
  rw [value21, value50, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ∈ [(29 : Vertex), (149 : Vertex), (159 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (157 : Vertex) [(29 : Vertex), (149 : Vertex), (159 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 21 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value21, value50, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (29 : Vertex) (149 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value50, value55, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (157 : Vertex) (149 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 171 = true ∨ valuation q 21 = true ∨ valuation q 55 = true := by
  rw [value21, value54, value55, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(29 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (149 : Vertex) [(29 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 171 = true ∨ valuation q 21 = true ∨ valuation q 50 = true := by
  rw [value21, value50, value54, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(29 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (159 : Vertex) [(29 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 23 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value23, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (31 : Vertex) (155 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 172 = true ∨ valuation q 53 = true ∨ valuation q 54 = true := by
  rw [value53, value54, value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(155 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (31 : Vertex) [(155 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 172 = true ∨ valuation q 23 = true ∨ valuation q 54 = true := by
  rw [value23, value54, value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(31 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (155 : Vertex) [(31 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 172 = true ∨ valuation q 23 = true ∨ valuation q 53 = true := by
  rw [value23, value53, value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(31 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (157 : Vertex) [(31 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 66 = false := by
  rw [value56, value57, value58, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 58 = true ∨ valuation q 66 = true := by
  rw [value56, value58, value66, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(194 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 57 = true ∨ valuation q 66 = true := by
  rw [value56, value57, value66, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(193 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (194 : Vertex) [(193 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 57 = true ∨ valuation q 58 = true := by
  rw [value56, value57, value58, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(193 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (208 : Vertex) [(193 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 39 = false ∨ valuation q 56 = false := by
  rw [value24, value39, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 39 = false ∨ valuation q 59 = false := by
  rw [value24, value39, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 39 = false ∨ valuation q 61 = false := by
  rw [value24, value39, value57, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 39 = false ∨ valuation q 67 = false := by
  rw [value24, value39, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 39 = false ∨ valuation q 106 = false := by
  rw [value24, value39, value57, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value24, value56, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 61 = false := by
  rw [value24, value56, value57, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 67 = false := by
  rw [value24, value56, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 56 = false ∨ valuation q 106 = false := by
  rw [value24, value56, value57, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value24, value57, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (195 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 59 = false ∨ valuation q 67 = false := by
  rw [value24, value57, value59, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (195 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 59 = false ∨ valuation q 106 = false := by
  rw [value24, value57, value59, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (195 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 24 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value24, value57, value61, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (201 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E115.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112115
