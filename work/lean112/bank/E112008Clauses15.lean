import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 86 = false ∨ valuation q 110 = false := by
  rw [value33, value86, value87, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value33, value87, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (419 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value33, value87, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (419 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value33, value87, value89, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (419 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value33, value87, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value33, value87, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 99 = false ∨ valuation q 110 = false := by
  rw [value33, value87, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value71, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value71, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 86 = false ∨ valuation q 99 = false := by
  rw [value71, value86, value87, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 86 = false ∨ valuation q 110 = false := by
  rw [value71, value86, value87, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value71, value87, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (419 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value71, value87, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (419 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value71, value87, value89, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (419 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value71, value87, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value71, value87, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 71 = false ∨ valuation q 99 = false ∨ valuation q 110 = false := by
  rw [value71, value87, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value86, value87, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (419 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value86, value87, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (419 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value86, value87, value89, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (419 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value86, value87, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value86, value87, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 99 = false ∨ valuation q 110 = false := by
  rw [value86, value87, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value87, value89, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value87, value89, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 110 = false := by
  rw [value87, value89, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (419 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 99 = false ∨ valuation q 110 = false := by
  rw [value87, value90, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (421 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 34 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value34, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (162 : Vertex) (416 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 34 = false ∨ valuation q 89 = false ∨ valuation q 100 = false := by
  rw [value34, value88, value89, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (162 : Vertex) (419 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 100 = false := by
  rw [value86, value88, value89, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (419 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 212 = true ∨ valuation q 34 = true ∨ valuation q 86 = true ∨ valuation q 100 = true := by
  rw [value34, value86, value88, value100, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(162 : Vertex), (416 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (419 : Vertex) [(162 : Vertex), (416 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 212 = true ∨ valuation q 34 = true ∨ valuation q 86 = true ∨ valuation q 89 = true := by
  rw [value34, value86, value88, value89, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(162 : Vertex), (416 : Vertex), (419 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (434 : Vertex) [(162 : Vertex), (416 : Vertex), (419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E008.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112008
