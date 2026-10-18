import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 34 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value34, value102, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 34 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value34, value102, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (488 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 34 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value34, value103, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 34 = false ∨ valuation q 105 = false ∨ valuation q 115 = false := by
  rw [value34, value103, value105, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (491 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 34 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value34, value103, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (233 : Vertex) (493 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value102, value103, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 115 = false := by
  rw [value102, value103, value105, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (491 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value102, value103, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (493 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value103, value105, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (491 : Vertex) (493 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 221 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 115 = true := by
  rw [value102, value103, value105, value107, value115, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (489 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(488 : Vertex), (491 : Vertex), (493 : Vertex), (505 : Vertex)] := by decide
  have hg := other_cover q (489 : Vertex) (233 : Vertex) [(488 : Vertex), (491 : Vertex), (493 : Vertex), (505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 67 = false ∨ valuation q 84 = false := by
  rw [value35, value67, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 67 = false ∨ valuation q 97 = false := by
  rw [value35, value67, value97, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 67 = false ∨ valuation q 102 = false := by
  rw [value35, value67, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 67 = false ∨ valuation q 105 = false := by
  rw [value35, value67, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 67 = false ∨ valuation q 108 = false := by
  rw [value35, value67, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (362 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 84 = false ∨ valuation q 97 = false := by
  rw [value35, value84, value97, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (426 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 84 = false ∨ valuation q 102 = false := by
  rw [value35, value84, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 84 = false ∨ valuation q 105 = false := by
  rw [value35, value84, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (426 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 84 = false ∨ valuation q 108 = false := by
  rw [value35, value84, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (426 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 97 = false ∨ valuation q 102 = false := by
  rw [value35, value97, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value35, value97, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value35, value97, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value35, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value35, value102, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 35 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value35, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (234 : Vertex) (491 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 84 = false ∨ valuation q 97 = false := by
  rw [value67, value84, value97, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (426 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 84 = false ∨ valuation q 102 = false := by
  rw [value67, value84, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 84 = false ∨ valuation q 105 = false := by
  rw [value67, value84, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (426 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 84 = false ∨ valuation q 108 = false := by
  rw [value67, value84, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (426 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 97 = false ∨ valuation q 102 = false := by
  rw [value67, value97, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value67, value97, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (482 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 67 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value67, value97, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (362 : Vertex) (482 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E104.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112104
