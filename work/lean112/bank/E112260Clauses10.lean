import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 40 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value40, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 40 = false ∨ valuation q 44 = false ∨ valuation q 64 = false := by
  rw [value40, value44, value45, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (204 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 40 = false ∨ valuation q 44 = false ∨ valuation q 111 = false := by
  rw [value40, value44, value45, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (204 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 64 = false := by
  rw [value40, value45, value46, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (207 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 40 = false ∨ valuation q 64 = false ∨ valuation q 111 = false := by
  rw [value40, value45, value64, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (237 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 64 = false := by
  rw [value44, value45, value46, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (204 : Vertex) (207 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 111 = false := by
  rw [value44, value45, value46, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (204 : Vertex) (207 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 64 = false ∨ valuation q 111 = false := by
  rw [value44, value45, value64, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (204 : Vertex) (237 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 172 = true ∨ valuation q 40 = true ∨ valuation q 44 = true ∨ valuation q 46 = true ∨ valuation q 64 = true := by
  rw [value40, value44, value45, value46, value64, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(197 : Vertex), (204 : Vertex), (207 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (461 : Vertex) [(197 : Vertex), (204 : Vertex), (207 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 46 = true := by
  rw [value46, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (207 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 9 = true ∨ valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 45 = true := by
  rw [value9, value41, value43, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ∈ [(79 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (207 : Vertex) [(79 : Vertex), (199 : Vertex), (203 : Vertex), (205 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 9 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value9, value41, value43, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (199 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 9 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value9, value41, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 9 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value9, value43, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value41, value43, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 9 = false ∨ valuation q 43 = false := by
  rw [value9, value43, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (207 : Vertex) (79 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 173 = true ∨ valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 45 = true := by
  rw [value41, value43, value45, value46, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(199 : Vertex), (203 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (79 : Vertex) [(199 : Vertex), (203 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 173 = true ∨ valuation q 9 = true ∨ valuation q 43 = true ∨ valuation q 45 = true := by
  rw [value9, value43, value45, value46, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(79 : Vertex), (203 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(79 : Vertex), (203 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 173 = true ∨ valuation q 9 = true ∨ valuation q 41 = true ∨ valuation q 45 = true := by
  rw [value9, value41, value45, value46, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(79 : Vertex), (199 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (203 : Vertex) [(79 : Vertex), (199 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 173 = true ∨ valuation q 9 = true ∨ valuation q 41 = true ∨ valuation q 43 = true := by
  rw [value9, value41, value43, value46, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(79 : Vertex), (199 : Vertex), (203 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [(79 : Vertex), (199 : Vertex), (203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 10 = false ∨ valuation q 36 = false ∨ valuation q 48 = false := by
  rw [value10, value36, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (192 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 10 = false ∨ valuation q 36 = false ∨ valuation q 49 = false := by
  rw [value10, value36, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (192 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 10 = false ∨ valuation q 36 = false ∨ valuation q 50 = false := by
  rw [value10, value36, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (192 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 10 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value10, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 10 = false ∨ valuation q 48 = false ∨ valuation q 50 = false := by
  rw [value10, value47, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 10 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value10, value47, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (210 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 36 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value36, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (192 : Vertex) (209 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 36 = false ∨ valuation q 48 = false ∨ valuation q 50 = false := by
  rw [value36, value47, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (192 : Vertex) (209 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 36 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value36, value47, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (192 : Vertex) (210 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value47, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (209 : Vertex) (210 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 36 = true ∨ valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 50 = true := by
  rw [value36, value47, value48, value49, value50, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(192 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (80 : Vertex) [(192 : Vertex), (209 : Vertex), (210 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 10 = true ∨ valuation q 36 = true ∨ valuation q 49 = true ∨ valuation q 50 = true := by
  rw [value10, value36, value47, value49, value50, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(80 : Vertex), (192 : Vertex), (210 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (209 : Vertex) [(80 : Vertex), (192 : Vertex), (210 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E260.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112260
