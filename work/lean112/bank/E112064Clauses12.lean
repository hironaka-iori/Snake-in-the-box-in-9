import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 66 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value66, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (322 : Vertex) (336 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 66 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value66, value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (322 : Vertex) (336 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 66 = false ∨ valuation q 74 = false ∨ valuation q 82 = false := by
  rw [value66, value74, value75, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (322 : Vertex) (336 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 66 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value66, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (322 : Vertex) (339 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 66 = false ∨ valuation q 76 = false ∨ valuation q 82 = false := by
  rw [value66, value75, value76, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (322 : Vertex) (339 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value74, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (336 : Vertex) (339 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 82 = false := by
  rw [value74, value75, value76, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (336 : Vertex) (339 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value74, value75, value78, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (336 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value75, value76, value78, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (339 : Vertex) (342 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 57 = false ∨ valuation q 67 = false := by
  rw [value10, value57, value67, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (339 : Vertex) (83 : Vertex) (275 : Vertex) (323 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 67 = false ∨ valuation q 75 = false := by
  rw [value10, value67, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (339 : Vertex) (83 : Vertex) (323 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 75 = false ∨ valuation q 111 = false := by
  rw [value10, value75, value76, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (339 : Vertex) (83 : Vertex) (338 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 57 = false ∨ valuation q 67 = false ∨ valuation q 111 = false := by
  rw [value57, value67, value76, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (339 : Vertex) (275 : Vertex) (323 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 57 = false ∨ valuation q 75 = false ∨ valuation q 79 = false := by
  rw [value57, value75, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (339 : Vertex) (275 : Vertex) (338 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 74 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value74, value77, value78, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (336 : Vertex) (342 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 194 = true ∨ valuation q 74 = true ∨ valuation q 83 = true := by
  rw [value74, value77, value83, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(336 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (342 : Vertex) [(336 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 194 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value74, value77, value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(336 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (348 : Vertex) [(336 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 85 = true := by
  rw [value77, value78, value79, value85, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(340 : Vertex), (343 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (338 : Vertex) [(340 : Vertex), (343 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 75 = true ∨ valuation q 79 = true ∨ valuation q 85 = true := by
  rw [value75, value78, value79, value85, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(338 : Vertex), (343 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (340 : Vertex) [(338 : Vertex), (343 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 85 = true := by
  rw [value75, value77, value78, value85, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(338 : Vertex), (340 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (343 : Vertex) [(338 : Vertex), (340 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value75, value77, value78, value79, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(338 : Vertex), (340 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (350 : Vertex) [(338 : Vertex), (340 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 59 = false ∨ valuation q 68 = false := by
  rw [value12, value59, value68, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 59 = false ∨ valuation q 76 = false := by
  rw [value12, value59, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 59 = false ∨ valuation q 78 = false := by
  rw [value12, value59, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 59 = false ∨ valuation q 86 = false := by
  rw [value12, value59, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 59 = false ∨ valuation q 113 = false := by
  rw [value12, value59, value79, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 68 = false ∨ valuation q 76 = false := by
  rw [value12, value68, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 68 = false ∨ valuation q 78 = false := by
  rw [value12, value68, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 68 = false ∨ valuation q 86 = false := by
  rw [value12, value68, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 68 = false ∨ valuation q 113 = false := by
  rw [value12, value68, value79, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value12, value76, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (339 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 12 = false ∨ valuation q 76 = false ∨ valuation q 86 = false := by
  rw [value12, value76, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (339 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E064.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112064
