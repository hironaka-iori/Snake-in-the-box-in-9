import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 213 = true ∨ valuation q 85 = true ∨ valuation q 90 = true := by
  rw [value85, value90, value91, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(421 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (425 : Vertex) [(421 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 33 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value33, value86, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 214 = true ∨ valuation q 86 = true ∨ valuation q 90 = true := by
  rw [value86, value90, value92, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(422 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (302 : Vertex) [(422 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 214 = true ∨ valuation q 33 = true ∨ valuation q 90 = true := by
  rw [value33, value90, value92, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(302 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (422 : Vertex) [(302 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 34 = false ∨ valuation q 74 = false ∨ valuation q 96 = false := by
  rw [value34, value74, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (401 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 34 = false ∨ valuation q 74 = false ∨ valuation q 117 = false := by
  rw [value34, value74, value93, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (401 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 74 = false ∨ valuation q 95 = false ∨ valuation q 117 = false := by
  rw [value74, value93, value95, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (401 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 215 = true ∨ valuation q 34 = true ∨ valuation q 74 = true ∨ valuation q 95 = true ∨ valuation q 117 = true := by
  rw [value34, value74, value93, value95, value117, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(305 : Vertex), (401 : Vertex), (435 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (437 : Vertex) [(305 : Vertex), (401 : Vertex), (435 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 216 = true ∨ valuation q 95 = true ∨ valuation q 97 = true := by
  rw [value94, value95, value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(435 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (418 : Vertex) [(435 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 216 = true ∨ valuation q 83 = true ∨ valuation q 97 = true := by
  rw [value83, value94, value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(418 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (435 : Vertex) [(418 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 216 = true ∨ valuation q 83 = true ∨ valuation q 95 = true := by
  rw [value83, value94, value95, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (438 : Vertex) → w ∈ [(418 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (438 : Vertex) [(418 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 35 = false ∨ valuation q 84 = false ∨ valuation q 93 = false := by
  rw [value35, value84, value93, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 35 = false ∨ valuation q 84 = false ∨ valuation q 94 = false := by
  rw [value35, value84, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 35 = false ∨ valuation q 84 = false ∨ valuation q 99 = false := by
  rw [value35, value84, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 35 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value35, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 35 = false ∨ valuation q 93 = false ∨ valuation q 99 = false := by
  rw [value35, value93, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 35 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value35, value94, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (434 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value84, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 99 = false := by
  rw [value84, value93, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 84 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value84, value94, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (434 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value93, value94, value95, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (434 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 217 = true ∨ valuation q 84 = true ∨ valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 99 = true := by
  rw [value84, value93, value94, value95, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(419 : Vertex), (433 : Vertex), (434 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (307 : Vertex) [(419 : Vertex), (433 : Vertex), (434 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 217 = true ∨ valuation q 35 = true ∨ valuation q 84 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value35, value84, value93, value94, value95, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(307 : Vertex), (419 : Vertex), (433 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (443 : Vertex) [(307 : Vertex), (419 : Vertex), (433 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 218 = true ∨ valuation q 93 = true := by
  rw [value93, value96, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(433 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (421 : Vertex) [(433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 37 = false ∨ valuation q 86 = false ∨ valuation q 94 = false := by
  rw [value37, value86, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (438 : Vertex) (310 : Vertex) (422 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 219 = true ∨ valuation q 86 = true ∨ valuation q 94 = true := by
  rw [value86, value94, value97, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(422 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (310 : Vertex) [(422 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 219 = true ∨ valuation q 37 = true ∨ valuation q 94 = true := by
  rw [value37, value94, value97, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(310 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (422 : Vertex) [(310 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 219 = true ∨ valuation q 37 = true ∨ valuation q 86 = true := by
  rw [value37, value86, value97, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(310 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (434 : Vertex) [(310 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 38 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value38, value87, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (312 : Vertex) (424 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 220 = true ∨ valuation q 87 = true ∨ valuation q 100 = true := by
  rw [value87, value98, value100, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (312 : Vertex) → w ∈ [(424 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (312 : Vertex) [(424 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 220 = true ∨ valuation q 38 = true ∨ valuation q 100 = true := by
  rw [value38, value98, value100, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(312 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(312 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 220 = true ∨ valuation q 38 = true ∨ valuation q 87 = true := by
  rw [value38, value87, value98, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(312 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (444 : Vertex) [(312 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block16 (q : Snake 81) (h : Conditions q) : B112E258.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112258
