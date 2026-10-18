import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 50 = false ∨ valuation q 81 = false ∨ valuation q 94 = false := by
  rw [value50, value81, value82, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 50 = false ∨ valuation q 81 = false ∨ valuation q 105 = false := by
  rw [value50, value81, value82, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 50 = false ∨ valuation q 85 = false ∨ valuation q 94 = false := by
  rw [value50, value82, value85, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 50 = false ∨ valuation q 85 = false ∨ valuation q 105 = false := by
  rw [value50, value82, value85, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 50 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value50, value82, value94, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 94 = false := by
  rw [value81, value82, value85, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 105 = false := by
  rw [value81, value82, value85, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 81 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value81, value82, value94, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value82, value85, value94, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (421 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 203 = true ∨ valuation q 50 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 94 = true ∨ valuation q 105 = true := by
  rw [value50, value81, value82, value85, value94, value105, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(289 : Vertex), (416 : Vertex), (421 : Vertex), (433 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (161 : Vertex) [(289 : Vertex), (416 : Vertex), (421 : Vertex), (433 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 14 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value14, value81, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (162 : Vertex) (416 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 14 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value14, value83, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (162 : Vertex) (422 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value81, value83, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (422 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value81, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 91 = false := by
  rw [value81, value84, value85, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 96 = false := by
  rw [value81, value84, value85, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value81, value84, value86, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 96 = false := by
  rw [value81, value84, value86, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value81, value84, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 91 = false := by
  rw [value84, value85, value86, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 96 = false := by
  rw [value84, value85, value86, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value84, value85, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value84, value86, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value85, value86, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 205 = true ∨ valuation q 81 = true ∨ valuation q 86 = true ∨ valuation q 91 = true ∨ valuation q 96 = true := by
  rw [value81, value84, value86, value91, value96, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(416 : Vertex), (422 : Vertex), (428 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (421 : Vertex) [(416 : Vertex), (422 : Vertex), (428 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 205 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 96 = true := by
  rw [value81, value84, value85, value86, value96, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(416 : Vertex), (421 : Vertex), (422 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (428 : Vertex) [(416 : Vertex), (421 : Vertex), (422 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value16, value82, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 97 = false := by
  rw [value16, value82, value85, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value16, value84, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 84 = false ∨ valuation q 97 = false := by
  rw [value16, value84, value85, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 87 = false ∨ valuation q 97 = false := by
  rw [value16, value85, value87, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (423 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value82, value84, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E026.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112026
