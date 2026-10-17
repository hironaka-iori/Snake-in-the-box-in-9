import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 75 = false := by
  rw [value57, value69, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (298 : Vertex) (354 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 115 = false := by
  rw [value57, value69, value74, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (298 : Vertex) (354 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 115 = false := by
  rw [value69, value74, value75, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (354 : Vertex) (363 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 115 = true := by
  rw [value69, value74, value75, value115, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (298 : Vertex) → w ∈ [(354 : Vertex), (363 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (298 : Vertex) [(354 : Vertex), (363 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 57 = true ∨ valuation q 75 = true ∨ valuation q 115 = true := by
  rw [value57, value74, value75, value115, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(298 : Vertex), (363 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (354 : Vertex) [(298 : Vertex), (363 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 115 = true := by
  rw [value57, value69, value74, value115, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(298 : Vertex), (354 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (363 : Vertex) [(298 : Vertex), (354 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 75 = true := by
  rw [value57, value69, value74, value75, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(298 : Vertex), (354 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (490 : Vertex) [(298 : Vertex), (354 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 58 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value58, value70, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (355 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 58 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value58, value70, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (355 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 58 = false ∨ valuation q 70 = false ∨ valuation q 77 = false := by
  rw [value58, value70, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (355 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 58 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value58, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (361 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 58 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value58, value73, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (361 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 58 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value58, value74, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (362 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value70, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (361 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value70, value73, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (361 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value70, value74, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (362 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value73, value74, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (361 : Vertex) (362 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 203 = true ∨ valuation q 58 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 74 = true := by
  rw [value58, value70, value73, value74, value75, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(299 : Vertex), (355 : Vertex), (361 : Vertex), (362 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (367 : Vertex) [(299 : Vertex), (355 : Vertex), (361 : Vertex), (362 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value72, value73, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (357 : Vertex) (361 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 117 = false := by
  rw [value72, value73, value76, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (357 : Vertex) (361 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 117 = false := by
  rw [value72, value76, value77, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (357 : Vertex) (367 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value73, value77, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (365 : Vertex) (361 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 72 = true ∨ valuation q 77 = true ∨ valuation q 117 = true := by
  rw [value72, value76, value77, value117, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(357 : Vertex), (367 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (361 : Vertex) [(357 : Vertex), (367 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 117 = true := by
  rw [value72, value73, value76, value117, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(357 : Vertex), (361 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (367 : Vertex) [(357 : Vertex), (361 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 85 = false := by
  rw [value75, value76, value77, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (363 : Vertex) (365 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 205 = true ∨ valuation q 76 = true ∨ valuation q 85 = true := by
  rw [value76, value77, value85, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(365 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (363 : Vertex) [(365 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 205 = true ∨ valuation q 75 = true ∨ valuation q 85 = true := by
  rw [value75, value77, value85, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(363 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (365 : Vertex) [(363 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 205 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value75, value76, value77, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(363 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (383 : Vertex) [(363 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value78, value79, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (369 : Vertex) (372 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 206 = true ∨ valuation q 81 = true ∨ valuation q 82 = true := by
  rw [value78, value81, value82, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (369 : Vertex) → w ∈ [(372 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (369 : Vertex) [(372 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 119 = false := by
  rw [value78, value79, value80, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (369 : Vertex) (368 : Vertex) (371 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 80 = true ∨ valuation q 119 = true := by
  rw [value79, value80, value119, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (369 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(371 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (369 : Vertex) (368 : Vertex) [(371 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : B112E034.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112034
