import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value71, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (327 : Vertex) (331 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 193 = true ∨ valuation q 57 = true ∨ valuation q 74 = true ∨ valuation q 75 = true := by
  rw [value57, value74, value75, value76, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(271 : Vertex), (331 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (327 : Vertex) [(271 : Vertex), (331 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 193 = true ∨ valuation q 57 = true ∨ valuation q 71 = true ∨ valuation q 74 = true := by
  rw [value57, value71, value74, value76, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(271 : Vertex), (327 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(271 : Vertex), (327 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 58 = false ∨ valuation q 69 = false ∨ valuation q 79 = false := by
  rw [value58, value69, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (273 : Vertex) (321 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 194 = true ∨ valuation q 58 = true ∨ valuation q 79 = true := by
  rw [value58, value77, value79, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(273 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (321 : Vertex) [(273 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value78, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (339 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 196 = true ∨ valuation q 59 = true ∨ valuation q 78 = true := by
  rw [value59, value78, value79, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(275 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(275 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 196 = true ∨ valuation q 59 = true ∨ valuation q 77 = true := by
  rw [value59, value77, value79, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(275 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (338 : Vertex) [(275 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 70 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value70, value78, value80, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (342 : Vertex) (326 : Vertex) (338 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 197 = true ∨ valuation q 78 = true ∨ valuation q 84 = true := by
  rw [value78, value80, value84, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(338 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (326 : Vertex) [(338 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 65 = true ∨ valuation q 78 = true ∨ valuation q 84 = true := by
  rw [value65, value78, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ∈ [(282 : Vertex), (338 : Vertex), (350 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (346 : Vertex) [(282 : Vertex), (338 : Vertex), (350 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 198 = true ∨ valuation q 78 = true ∨ valuation q 84 = true := by
  rw [value78, value81, value84, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(338 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (282 : Vertex) [(338 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 198 = true ∨ valuation q 65 = true ∨ valuation q 84 = true := by
  rw [value65, value81, value84, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(282 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (338 : Vertex) [(282 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 198 = true ∨ valuation q 65 = true ∨ valuation q 78 = true := by
  rw [value65, value78, value81, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(282 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (350 : Vertex) [(282 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = true ∨ valuation q 84 = true := by
  rw [value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ∈ [(349 : Vertex), (350 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (348 : Vertex) [(349 : Vertex), (350 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 199 = true ∨ valuation q 84 = true := by
  rw [value82, value84, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (349 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 199 = true ∨ valuation q 83 = true := by
  rw [value82, value83, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(349 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 82 = true := by
  rw [value82, value83, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (333 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 200 = true ∨ valuation q 75 = true := by
  rw [value75, value83, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (348 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value80, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (346 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 201 = true ∨ valuation q 80 = true ∨ valuation q 82 = true := by
  rw [value80, value82, value84, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(342 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (346 : Vertex) [(342 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 45 = false ∨ valuation q 90 = false := by
  rw [value15, value45, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (256 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 45 = false ∨ valuation q 95 = false := by
  rw [value15, value45, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (256 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value15, value85, value86, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 86 = false ∨ valuation q 95 = false := by
  rw [value15, value85, value86, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (385 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 15 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value15, value85, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (128 : Vertex) (392 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 45 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value45, value85, value86, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (256 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 45 = false ∨ valuation q 86 = false ∨ valuation q 95 = false := by
  rw [value45, value85, value86, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (256 : Vertex) (385 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 45 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value45, value85, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (256 : Vertex) (392 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value85, value86, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (392 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 45 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 95 = true := by
  rw [value45, value85, value86, value90, value95, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(256 : Vertex), (385 : Vertex), (392 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (128 : Vertex) [(256 : Vertex), (385 : Vertex), (392 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 15 = true ∨ valuation q 45 = true ∨ valuation q 90 = true ∨ valuation q 95 = true := by
  rw [value15, value45, value85, value90, value95, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (392 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (385 : Vertex) [(128 : Vertex), (256 : Vertex), (392 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E207.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112207
