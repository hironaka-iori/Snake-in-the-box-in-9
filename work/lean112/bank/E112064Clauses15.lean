import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 115 = false := by
  rw [value80, value81, value84, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (344 : Vertex) (349 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 199 = true ∨ valuation q 80 = true ∨ valuation q 85 = true := by
  rw [value80, value82, value85, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(344 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (338 : Vertex) [(344 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 199 = true ∨ valuation q 75 = true ∨ valuation q 85 = true := by
  rw [value75, value82, value85, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(338 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (344 : Vertex) [(338 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 199 = true ∨ valuation q 75 = true ∨ valuation q 80 = true := by
  rw [value75, value80, value82, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(338 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (350 : Vertex) [(338 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 80 = false ∨ valuation q 85 = false := by
  rw [value71, value80, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (332 : Vertex) (344 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 77 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value77, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (340 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value80, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (344 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 77 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 85 = true := by
  rw [value77, value80, value83, value84, value85, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(340 : Vertex), (344 : Vertex), (349 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (332 : Vertex) [(340 : Vertex), (344 : Vertex), (349 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 71 = true ∨ valuation q 80 = true ∨ valuation q 84 = true ∨ valuation q 85 = true := by
  rw [value71, value80, value83, value84, value85, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(332 : Vertex), (344 : Vertex), (349 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (340 : Vertex) [(332 : Vertex), (344 : Vertex), (349 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 71 = true ∨ valuation q 77 = true ∨ valuation q 84 = true ∨ valuation q 85 = true := by
  rw [value71, value77, value83, value84, value85, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(332 : Vertex), (340 : Vertex), (349 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (344 : Vertex) [(332 : Vertex), (340 : Vertex), (349 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 71 = true ∨ valuation q 77 = true ∨ valuation q 80 = true ∨ valuation q 85 = true := by
  rw [value71, value77, value80, value83, value85, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(332 : Vertex), (340 : Vertex), (344 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (349 : Vertex) [(332 : Vertex), (340 : Vertex), (344 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 71 = true ∨ valuation q 77 = true ∨ valuation q 80 = true ∨ valuation q 84 = true := by
  rw [value71, value77, value80, value83, value84, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(332 : Vertex), (340 : Vertex), (344 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(332 : Vertex), (340 : Vertex), (344 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value15, value72, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (333 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 72 = false ∨ valuation q 83 = false := by
  rw [value15, value72, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (333 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 72 = false ∨ valuation q 86 = false := by
  rw [value15, value72, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (333 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value15, value81, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (345 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 81 = false ∨ valuation q 86 = false := by
  rw [value15, value81, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (345 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value15, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value72, value81, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (345 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 86 = false := by
  rw [value72, value81, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (345 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value72, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (348 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 201 = true ∨ valuation q 72 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true := by
  rw [value72, value81, value83, value84, value86, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(333 : Vertex), (345 : Vertex), (348 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (93 : Vertex) [(333 : Vertex), (345 : Vertex), (348 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 201 = true ∨ valuation q 15 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true := by
  rw [value15, value81, value83, value84, value86, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(93 : Vertex), (345 : Vertex), (348 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (333 : Vertex) [(93 : Vertex), (345 : Vertex), (348 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 62 = false ∨ valuation q 78 = false := by
  rw [value16, value62, value78, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (286 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 62 = false ∨ valuation q 82 = false := by
  rw [value16, value62, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (286 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 62 = false ∨ valuation q 83 = false := by
  rw [value16, value62, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (286 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 62 = false ∨ valuation q 86 = false := by
  rw [value16, value62, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (286 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 62 = false ∨ valuation q 116 = false := by
  rw [value16, value62, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (286 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value16, value78, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value16, value78, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (342 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value16, value78, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 16 = false ∨ valuation q 78 = false ∨ valuation q 116 = false := by
  rw [value16, value78, value85, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (94 : Vertex) (342 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E064.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112064
