import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 29 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value29, value87, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value82, value87, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (425 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 88 = false ∨ valuation q 98 = false := by
  rw [value82, value87, value88, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (425 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value82, value87, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 98 = false ∨ valuation q 113 = false := by
  rw [value82, value87, value98, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (416 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value87, value88, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (425 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 113 = false := by
  rw [value87, value90, value98, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (428 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 30 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value30, value87, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (297 : Vertex) (424 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value87, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (424 : Vertex) (427 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 91 = true := by
  rw [value87, value88, value89, value91, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(424 : Vertex), (427 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (297 : Vertex) [(424 : Vertex), (427 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 30 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value30, value87, value88, value91, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(297 : Vertex), (424 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (427 : Vertex) [(297 : Vertex), (424 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 30 = true ∨ valuation q 87 = true ∨ valuation q 89 = true := by
  rw [value30, value87, value88, value89, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (429 : Vertex) → w ∈ [(297 : Vertex), (424 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (429 : Vertex) [(297 : Vertex), (424 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 31 = false ∨ valuation q 84 = false ∨ valuation q 88 = false := by
  rw [value31, value84, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (419 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 31 = false ∨ valuation q 84 = false ∨ valuation q 99 = false := by
  rw [value31, value84, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (419 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 31 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value31, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (425 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value84, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (419 : Vertex) (425 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 211 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 99 = true := by
  rw [value84, value88, value89, value99, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(419 : Vertex), (425 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (299 : Vertex) [(419 : Vertex), (425 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 211 = true ∨ valuation q 31 = true ∨ valuation q 88 = true ∨ valuation q 99 = true := by
  rw [value31, value88, value89, value99, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(299 : Vertex), (425 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (419 : Vertex) [(299 : Vertex), (425 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 211 = true ∨ valuation q 31 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value31, value84, value88, value89, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(299 : Vertex), (419 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (443 : Vertex) [(299 : Vertex), (419 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 32 = false ∨ valuation q 71 = false ∨ valuation q 87 = false := by
  rw [value32, value71, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (300 : Vertex) (396 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 32 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value32, value87, value90, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (300 : Vertex) (424 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 32 = false ∨ valuation q 92 = false ∨ valuation q 100 = false := by
  rw [value32, value90, value92, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (300 : Vertex) (430 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 32 = false ∨ valuation q 100 = false ∨ valuation q 115 = false := by
  rw [value32, value90, value100, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (300 : Vertex) (444 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 71 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value71, value87, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (396 : Vertex) (424 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 71 = false ∨ valuation q 87 = false ∨ valuation q 115 = false := by
  rw [value71, value87, value90, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (396 : Vertex) (424 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 71 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value71, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (396 : Vertex) (429 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 71 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value71, value90, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (396 : Vertex) (429 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 71 = false ∨ valuation q 92 = false ∨ valuation q 100 = false := by
  rw [value71, value90, value92, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (396 : Vertex) (430 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 71 = false ∨ valuation q 100 = false ∨ valuation q 115 = false := by
  rw [value71, value90, value100, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (396 : Vertex) (444 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 100 = false ∨ valuation q 115 = false := by
  rw [value90, value92, value100, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (430 : Vertex) (444 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value85, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (421 : Vertex) (425 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 213 = true ∨ valuation q 88 = true ∨ valuation q 90 = true := by
  rw [value88, value90, value91, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(425 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (421 : Vertex) [(425 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E258.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112258
