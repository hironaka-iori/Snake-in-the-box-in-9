import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 40 = false ∨ valuation q 60 = false := by
  rw [value22, value40, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (145 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 40 = false ∨ valuation q 64 = false := by
  rw [value22, value40, value58, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (145 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 40 = false ∨ valuation q 115 = false := by
  rw [value22, value40, value58, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (145 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value22, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (211 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value22, value58, value59, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (211 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 59 = false ∨ valuation q 115 = false := by
  rw [value22, value58, value59, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (211 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value22, value58, value60, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (213 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 60 = false ∨ valuation q 115 = false := by
  rw [value22, value58, value60, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (213 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value22, value58, value64, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (217 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value40, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (211 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value40, value58, value59, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (211 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 59 = false ∨ valuation q 115 = false := by
  rw [value40, value58, value59, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (211 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value40, value58, value60, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (213 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 60 = false ∨ valuation q 115 = false := by
  rw [value40, value58, value60, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (213 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value40, value58, value64, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (217 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value58, value59, value60, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (211 : Vertex) (213 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 115 = false := by
  rw [value58, value59, value60, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (211 : Vertex) (213 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value58, value59, value64, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (211 : Vertex) (217 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 64 = false ∨ valuation q 115 = false := by
  rw [value58, value60, value64, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (213 : Vertex) (217 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 182 = true ∨ valuation q 22 = true ∨ valuation q 40 = true ∨ valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 115 = true := by
  rw [value22, value40, value58, value59, value60, value115, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(81 : Vertex), (145 : Vertex), (211 : Vertex), (213 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (217 : Vertex) [(81 : Vertex), (145 : Vertex), (211 : Vertex), (213 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 59 = true := by
  rw [value59, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (211 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 24 = false ∨ valuation q 58 = false ∨ valuation q 62 = false := by
  rw [value24, value58, value59, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (209 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 24 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value24, value59, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (215 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value58, value59, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (209 : Vertex) (215 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 24 = false ∨ valuation q 65 = false := by
  rw [value24, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (211 : Vertex) (83 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 58 = true ∨ valuation q 62 = true ∨ valuation q 65 = true := by
  rw [value58, value59, value62, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(209 : Vertex), (215 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (83 : Vertex) [(209 : Vertex), (215 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 24 = true ∨ valuation q 62 = true ∨ valuation q 65 = true := by
  rw [value24, value59, value62, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(83 : Vertex), (215 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (209 : Vertex) [(83 : Vertex), (215 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 24 = true ∨ valuation q 58 = true ∨ valuation q 65 = true := by
  rw [value24, value58, value59, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(83 : Vertex), (209 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (215 : Vertex) [(83 : Vertex), (209 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 24 = true ∨ valuation q 58 = true ∨ valuation q 62 = true := by
  rw [value24, value58, value59, value62, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(83 : Vertex), (209 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (219 : Vertex) [(83 : Vertex), (209 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 60 = true := by
  rw [value60, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (213 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 50 = true ∨ valuation q 58 = true ∨ valuation q 62 = true ∨ valuation q 118 = true := by
  rw [value50, value58, value60, value62, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ∈ [(197 : Vertex), (209 : Vertex), (215 : Vertex), (469 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (213 : Vertex) [(197 : Vertex), (209 : Vertex), (215 : Vertex), (469 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 118 = false := by
  rw [value58, value60, value62, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (209 : Vertex) (215 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E105.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112105
