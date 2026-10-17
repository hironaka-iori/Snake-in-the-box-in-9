import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 214 = true ∨ valuation q 14 = true ∨ valuation q 74 = true ∨ valuation q 83 = true ∨ valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 111 = true := by
  rw [value14, value74, value83, value87, value88, value90, value111, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(89 : Vertex), (281 : Vertex), (337 : Vertex), (347 : Vertex), (349 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (329 : Vertex) [(89 : Vertex), (281 : Vertex), (337 : Vertex), (347 : Vertex), (349 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 98 = false ∨ valuation q 112 = false := by
  rw [value88, value92, value98, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (351 : Vertex) (379 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 215 = true ∨ valuation q 92 = true ∨ valuation q 98 = true ∨ valuation q 112 = true := by
  rw [value88, value92, value98, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(351 : Vertex), (379 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (345 : Vertex) [(351 : Vertex), (379 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 98 = true ∨ valuation q 112 = true := by
  rw [value87, value88, value98, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(345 : Vertex), (379 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (351 : Vertex) [(345 : Vertex), (379 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 112 = true := by
  rw [value87, value88, value92, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(345 : Vertex), (351 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (379 : Vertex) [(345 : Vertex), (351 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 98 = true := by
  rw [value87, value88, value92, value98, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(345 : Vertex), (351 : Vertex), (379 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (475 : Vertex) [(345 : Vertex), (351 : Vertex), (379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 90 = true ∨ valuation q 91 = true := by
  rw [value89, value90, value91, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(349 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (476 : Vertex) [(349 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 16 = false ∨ valuation q 75 = false ∨ valuation q 80 = false := by
  rw [value16, value75, value80, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (285 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 16 = false ∨ valuation q 75 = false ∨ valuation q 85 = false := by
  rw [value16, value75, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (285 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 16 = false ∨ valuation q 75 = false ∨ valuation q 87 = false := by
  rw [value16, value75, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (285 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 16 = false ∨ valuation q 75 = false ∨ valuation q 114 = false := by
  rw [value16, value75, value90, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (93 : Vertex) (285 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 85 = false := by
  rw [value75, value80, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (285 : Vertex) (333 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value75, value80, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (285 : Vertex) (333 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 92 = false := by
  rw [value75, value80, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (285 : Vertex) (333 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 114 = false := by
  rw [value75, value80, value90, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (285 : Vertex) (333 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 75 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value75, value85, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (285 : Vertex) (341 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 75 = false ∨ valuation q 87 = false ∨ valuation q 114 = false := by
  rw [value75, value87, value90, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (285 : Vertex) (345 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value80, value85, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (341 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value80, value87, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (345 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 80 = false ∨ valuation q 92 = false ∨ valuation q 99 = false := by
  rw [value80, value90, value92, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (351 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value18, value88, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (95 : Vertex) (347 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value18, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (95 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value88, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (347 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 101 = false := by
  rw [value88, value90, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (347 : Vertex) (349 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value88, value91, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (347 : Vertex) (350 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value90, value91, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (349 : Vertex) (350 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 80 = true ∨ valuation q 94 = true ∨ valuation q 99 = true := by
  rw [value80, value93, value94, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ∈ [(333 : Vertex), (367 : Vertex), (381 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (365 : Vertex) [(333 : Vertex), (367 : Vertex), (381 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 80 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value80, value93, value94, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (333 : Vertex) (367 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 220 = true ∨ valuation q 94 = true ∨ valuation q 99 = true := by
  rw [value93, value94, value99, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(367 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (333 : Vertex) [(367 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 220 = true ∨ valuation q 80 = true ∨ valuation q 99 = true := by
  rw [value80, value93, value99, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(333 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (367 : Vertex) [(333 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 93 = false ∨ valuation q 101 = false ∨ valuation q 116 = false := by
  rw [value93, value94, value101, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (365 : Vertex) (383 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 221 = true ∨ valuation q 93 = true ∨ valuation q 101 = true := by
  rw [value93, value94, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(365 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (495 : Vertex) [(365 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E256.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112256
