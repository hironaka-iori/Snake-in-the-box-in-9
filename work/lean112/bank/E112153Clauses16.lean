import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 87 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value87, value110, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (394 : Vertex) (462 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 108 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value108, value110, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (456 : Vertex) (459 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 108 = false ∨ valuation q 111 = false ∨ valuation q 121 = false := by
  rw [value108, value110, value111, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (456 : Vertex) (459 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 108 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value108, value110, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (456 : Vertex) (462 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value110, value111, value113, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (459 : Vertex) (462 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 234 = true ∨ valuation q 108 = true ∨ valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 121 = true := by
  rw [value108, value110, value111, value113, value121, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(456 : Vertex), (459 : Vertex), (462 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (394 : Vertex) [(456 : Vertex), (459 : Vertex), (462 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 104 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value104, value109, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value109, value110, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value109, value110, value111, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value109, value111, value114, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 235 = true ∨ valuation q 104 = true ∨ valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 114 = true := by
  rw [value104, value109, value110, value111, value114, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(451 : Vertex), (457 : Vertex), (458 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (475 : Vertex) [(451 : Vertex), (457 : Vertex), (458 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 89 = false ∨ valuation q 106 = false ∨ valuation q 114 = false := by
  rw [value89, value106, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 89 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value89, value109, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (461 : Vertex) (397 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 106 = true ∨ valuation q 109 = true ∨ valuation q 114 = true := by
  rw [value106, value109, value112, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(453 : Vertex), (457 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (397 : Vertex) [(453 : Vertex), (457 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 89 = true ∨ valuation q 109 = true ∨ valuation q 114 = true := by
  rw [value89, value109, value112, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(397 : Vertex), (457 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (453 : Vertex) [(397 : Vertex), (457 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 89 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value89, value106, value112, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(397 : Vertex), (453 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (457 : Vertex) [(397 : Vertex), (453 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 89 = true ∨ valuation q 106 = true ∨ valuation q 109 = true := by
  rw [value89, value106, value109, value112, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(397 : Vertex), (453 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (463 : Vertex) [(397 : Vertex), (453 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 36 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value36, value72, value90, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 36 = false ∨ valuation q 72 = false ∨ valuation q 110 = false := by
  rw [value36, value72, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (334 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 36 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value36, value90, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (398 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 36 = false ∨ valuation q 110 = false ∨ valuation q 124 = false := by
  rw [value36, value110, value113, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (458 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 72 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value72, value90, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 72 = false ∨ valuation q 90 = false ∨ valuation q 114 = false := by
  rw [value72, value90, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 72 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value72, value110, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (334 : Vertex) (458 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value90, value110, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (458 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 110 = false ∨ valuation q 114 = false ∨ valuation q 124 = false := by
  rw [value110, value113, value114, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (458 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 72 = true ∨ valuation q 90 = true ∨ valuation q 110 = true ∨ valuation q 114 = true ∨ valuation q 124 = true := by
  rw [value72, value90, value110, value113, value114, value124, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(334 : Vertex), (398 : Vertex), (458 : Vertex), (463 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (206 : Vertex) [(334 : Vertex), (398 : Vertex), (458 : Vertex), (463 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 37 = false ∨ valuation q 73 = false ∨ valuation q 91 = false := by
  rw [value37, value73, value91, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 37 = false ∨ valuation q 73 = false ∨ valuation q 107 = false := by
  rw [value37, value73, value107, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (335 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 37 = false ∨ valuation q 73 = false ∨ valuation q 111 = false := by
  rw [value37, value73, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (335 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 37 = false ∨ valuation q 73 = false ∨ valuation q 112 = false := by
  rw [value37, value73, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (335 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 37 = false ∨ valuation q 73 = false ∨ valuation q 113 = false := by
  rw [value37, value73, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (463 : Vertex) (207 : Vertex) (335 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E153.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112153
