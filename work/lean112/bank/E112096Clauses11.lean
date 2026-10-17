import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 41 = false ∨ valuation q 102 = false ∨ valuation q 116 = false := by
  rw [value41, value102, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (205 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 41 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value41, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (205 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 41 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value41, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (205 : Vertex) (460 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 41 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value41, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (205 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value66, value85, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (397 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 104 = false := by
  rw [value66, value85, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (397 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 107 = false := by
  rw [value66, value85, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (397 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 116 = false := by
  rw [value66, value85, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (397 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value66, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (457 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value66, value102, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 102 = false ∨ valuation q 116 = false := by
  rw [value66, value102, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value66, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 66 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value66, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (333 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value85, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (457 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value85, value102, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 102 = false ∨ valuation q 116 = false := by
  rw [value85, value102, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (457 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value85, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value85, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (460 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 85 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value85, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value102, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (457 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value102, value104, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (457 : Vertex) (460 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 102 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value102, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (457 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 104 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value104, value105, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (460 : Vertex) (463 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 86 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value86, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (460 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 86 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value86, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 104 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value104, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (460 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value101, value103, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (455 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value103, value105, value106, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(459 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (455 : Vertex) [(459 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value101, value105, value106, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(455 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (459 : Vertex) [(455 : Vertex), (461 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value101, value103, value106, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (461 : Vertex) [(455 : Vertex), (459 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 118 = true := by
  rw [value101, value103, value105, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (462 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value101, value103, value105, value106, value107, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (479 : Vertex) [(455 : Vertex), (459 : Vertex), (461 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E096.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112096
