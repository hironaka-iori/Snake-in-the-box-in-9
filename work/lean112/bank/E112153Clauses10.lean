import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value86, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (396 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value86, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (396 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 112 = false := by
  rw [value86, value88, value89, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (396 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value86, value89, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (399 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 112 = false := by
  rw [value86, value89, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (393 : Vertex) (399 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value88, value89, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (396 : Vertex) (399 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 112 = false := by
  rw [value88, value89, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (396 : Vertex) (399 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value88, value89, value99, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (396 : Vertex) (413 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value89, value91, value99, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (399 : Vertex) (413 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 55 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 99 = true ∨ valuation q 112 = true := by
  rw [value55, value86, value88, value89, value91, value99, value112, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(269 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (141 : Vertex) [(269 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex), (413 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 20 = true ∨ valuation q 55 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 112 = true := by
  rw [value20, value55, value86, value88, value89, value91, value112, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(141 : Vertex), (269 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(141 : Vertex), (269 : Vertex), (393 : Vertex), (396 : Vertex), (399 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value87, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (396 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value87, value88, value90, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (396 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 113 = false := by
  rw [value87, value88, value90, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (396 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value87, value90, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (399 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value87, value90, value91, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (399 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value87, value90, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value88, value90, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (396 : Vertex) (399 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value88, value90, value91, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (396 : Vertex) (399 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value88, value90, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (396 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value90, value91, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (399 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 56 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value56, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 56 = false ∨ valuation q 89 = false ∨ valuation q 114 = false := by
  rw [value56, value89, value91, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (397 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 114 = false := by
  rw [value89, value90, value91, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (397 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value89, value91, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (397 : Vertex) (415 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 90 = true ∨ valuation q 101 = true ∨ valuation q 114 = true := by
  rw [value85, value89, value90, value91, value101, value114, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(391 : Vertex), (397 : Vertex), (398 : Vertex), (415 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (271 : Vertex) [(391 : Vertex), (397 : Vertex), (398 : Vertex), (415 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 56 = true ∨ valuation q 89 = true ∨ valuation q 90 = true ∨ valuation q 101 = true ∨ valuation q 114 = true := by
  rw [value56, value89, value90, value91, value101, value114, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(271 : Vertex), (397 : Vertex), (398 : Vertex), (415 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(271 : Vertex), (397 : Vertex), (398 : Vertex), (415 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 56 = true ∨ valuation q 85 = true ∨ valuation q 90 = true ∨ valuation q 101 = true ∨ valuation q 114 = true := by
  rw [value56, value85, value90, value91, value101, value114, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(271 : Vertex), (391 : Vertex), (398 : Vertex), (415 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (397 : Vertex) [(271 : Vertex), (391 : Vertex), (398 : Vertex), (415 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 56 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 90 = true ∨ valuation q 114 = true := by
  rw [value56, value85, value89, value90, value91, value114, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(271 : Vertex), (391 : Vertex), (397 : Vertex), (398 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (415 : Vertex) [(271 : Vertex), (391 : Vertex), (397 : Vertex), (398 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 82 = false := by
  rw [value21, value57, value82, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (272 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 93 = false := by
  rw [value21, value57, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (272 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 94 = false := by
  rw [value21, value57, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (272 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E153.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112153
