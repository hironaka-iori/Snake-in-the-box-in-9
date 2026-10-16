import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 56 = false ∨ valuation q 80 = false ∨ valuation q 104 = false := by
  rw [value56, value80, value81, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 56 = false ∨ valuation q 84 = false ∨ valuation q 93 = false := by
  rw [value56, value81, value84, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 56 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value56, value81, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 56 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value56, value81, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 93 = false := by
  rw [value80, value81, value84, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value80, value81, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value80, value81, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value81, value84, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (421 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value80, value82, value85, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (422 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 105 = false := by
  rw [value80, value82, value85, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (422 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 88 = false ∨ valuation q 105 = false := by
  rw [value80, value82, value88, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (426 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 105 = false := by
  rw [value82, value85, value88, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (422 : Vertex) (426 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 204 = true ∨ valuation q 80 = true ∨ valuation q 85 = true ∨ valuation q 105 = true := by
  rw [value80, value82, value85, value105, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(416 : Vertex), (422 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (426 : Vertex) [(416 : Vertex), (422 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value80, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 90 = false := by
  rw [value80, value83, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 95 = false := by
  rw [value80, value83, value84, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 90 = false := by
  rw [value80, value83, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value80, value83, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value80, value83, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 90 = false := by
  rw [value83, value84, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value83, value84, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value83, value84, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value83, value85, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 205 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 85 = true ∨ valuation q 95 = true := by
  rw [value80, value83, value84, value85, value95, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(416 : Vertex), (421 : Vertex), (422 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (428 : Vertex) [(416 : Vertex), (421 : Vertex), (422 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 57 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value57, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (293 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value81, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 96 = false := by
  rw [value81, value83, value84, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 83 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value83, value84, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (420 : Vertex) (437 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 206 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 96 = true ∨ valuation q 107 = true := by
  rw [value81, value83, value84, value86, value96, value107, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (293 : Vertex) [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 206 = true ∨ valuation q 57 = true ∨ valuation q 81 = true ∨ valuation q 86 = true ∨ valuation q 96 = true ∨ valuation q 107 = true := by
  rw [value57, value81, value84, value86, value96, value107, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(293 : Vertex), (417 : Vertex), (423 : Vertex), (437 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (420 : Vertex) [(293 : Vertex), (417 : Vertex), (423 : Vertex), (437 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 206 = true ∨ valuation q 57 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 107 = true := by
  rw [value57, value81, value83, value84, value86, value107, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(293 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(293 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 206 = true ∨ valuation q 57 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 96 = true := by
  rw [value57, value81, value83, value84, value86, value96, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(293 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (485 : Vertex) [(293 : Vertex), (417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem block10 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.First112
