import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 80 = true ∨ valuation q 87 = true := by
  rw [value78, value80, value87, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(333 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (73 : Vertex) [(333 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 6 = true ∨ valuation q 87 = true := by
  rw [value6, value78, value87, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(73 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (333 : Vertex) [(73 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 6 = true ∨ valuation q 80 = true := by
  rw [value6, value78, value80, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(73 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (345 : Vertex) [(73 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 79 = true := by
  rw [value79, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (330 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 81 = true ∨ valuation q 102 = true := by
  rw [value79, value81, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ∈ [(334 : Vertex), (458 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (330 : Vertex) [(334 : Vertex), (458 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 102 = true := by
  rw [value79, value102, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(458 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (334 : Vertex) [(458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 81 = true := by
  rw [value79, value81, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(334 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (458 : Vertex) [(334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value78, value80, value90, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (349 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 90 = false ∨ valuation q 105 = false := by
  rw [value78, value80, value90, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (349 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 78 = false ∨ valuation q 93 = false ∨ valuation q 105 = false := by
  rw [value78, value80, value93, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (365 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 105 = false := by
  rw [value80, value90, value93, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (349 : Vertex) (365 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 207 = true ∨ valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 105 = true := by
  rw [value80, value90, value93, value105, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(349 : Vertex), (365 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (329 : Vertex) [(349 : Vertex), (365 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 207 = true ∨ valuation q 78 = true ∨ valuation q 90 = true ∨ valuation q 105 = true := by
  rw [value78, value80, value90, value105, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(329 : Vertex), (349 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (365 : Vertex) [(329 : Vertex), (349 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 207 = true ∨ valuation q 78 = true ∨ valuation q 90 = true ∨ valuation q 93 = true := by
  rw [value78, value80, value90, value93, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(329 : Vertex), (349 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (461 : Vertex) [(329 : Vertex), (349 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 208 = true ∨ valuation q 91 = true := by
  rw [value81, value91, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (330 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 10 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 106 = true := by
  rw [value10, value82, value83, value84, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ∈ [(80 : Vertex), (337 : Vertex), (338 : Vertex), (464 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (336 : Vertex) [(80 : Vertex), (337 : Vertex), (338 : Vertex), (464 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 10 = false ∨ valuation q 83 = false := by
  rw [value10, value83, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (336 : Vertex) (80 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 10 = false ∨ valuation q 84 = false := by
  rw [value10, value84, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (336 : Vertex) (80 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 10 = false ∨ valuation q 106 = false := by
  rw [value10, value106, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (336 : Vertex) (80 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value83, value84, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (336 : Vertex) (337 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 83 = false ∨ valuation q 106 = false := by
  rw [value83, value106, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (336 : Vertex) (337 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 84 = false ∨ valuation q 106 = false := by
  rw [value84, value106, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (336 : Vertex) (338 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 82 = true := by
  rw [value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 209 = true := by
  rw [value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value82, value83, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (336 : Vertex) (341 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 210 = true ∨ valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 107 = true := by
  rw [value83, value85, value87, value107, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(341 : Vertex), (345 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (336 : Vertex) [(341 : Vertex), (345 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = false ∨ valuation q 90 = false ∨ valuation q 96 = false := by
  rw [value83, value85, value90, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (337 : Vertex) (349 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = false ∨ valuation q 90 = false ∨ valuation q 109 = false := by
  rw [value83, value85, value90, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (337 : Vertex) (349 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value83, value85, value96, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (337 : Vertex) (373 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 212 = true ∨ valuation q 90 = true ∨ valuation q 96 = true ∨ valuation q 109 = true := by
  rw [value85, value90, value96, value109, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(349 : Vertex), (373 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (337 : Vertex) [(349 : Vertex), (373 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 212 = true ∨ valuation q 83 = true ∨ valuation q 90 = true ∨ valuation q 109 = true := by
  rw [value83, value85, value90, value109, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(337 : Vertex), (349 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (373 : Vertex) [(337 : Vertex), (349 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 212 = true ∨ valuation q 83 = true ∨ valuation q 90 = true ∨ valuation q 96 = true := by
  rw [value83, value85, value90, value96, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(337 : Vertex), (349 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (469 : Vertex) [(337 : Vertex), (349 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block16 (q : Snake 81) (h : Conditions q) : B112E256.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112256
