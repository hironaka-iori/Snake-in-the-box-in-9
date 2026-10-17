import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 54 = true ∨ valuation q 70 = true := by
  rw [value54, value70, value72, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(220 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (236 : Vertex) [(220 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 199 = true ∨ valuation q 54 = true ∨ valuation q 63 = true := by
  rw [value54, value63, value72, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(220 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (248 : Vertex) [(220 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 73 = true := by
  rw [value73, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (255 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 35 = true ∨ valuation q 71 = true := by
  rw [value35, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ∈ [(127 : Vertex), (251 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (255 : Vertex) [(127 : Vertex), (251 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 35 = false ∨ valuation q 71 = false := by
  rw [value35, value71, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (255 : Vertex) (127 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 71 = true := by
  rw [value71, value73, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (127 : Vertex) → w ∈ [(251 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (127 : Vertex) [(251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 200 = true ∨ valuation q 35 = true := by
  rw [value35, value73, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(127 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (251 : Vertex) [(127 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 74 = true := by
  rw [value74, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (257 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = true ∨ valuation q 78 = true := by
  rw [value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ∈ [(261 : Vertex), (321 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (257 : Vertex) [(261 : Vertex), (321 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value75, value78, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (257 : Vertex) (261 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 201 = true ∨ valuation q 78 = true := by
  rw [value74, value78, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 201 = true ∨ valuation q 75 = true := by
  rw [value74, value75, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(261 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (321 : Vertex) [(261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value74, value75, value76, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (293 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 76 = true ∨ valuation q 81 = true := by
  rw [value75, value76, value81, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(293 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (257 : Vertex) [(293 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 74 = true ∨ valuation q 81 = true := by
  rw [value74, value75, value81, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(257 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (293 : Vertex) [(257 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 74 = true ∨ valuation q 76 = true := by
  rw [value74, value75, value76, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(257 : Vertex), (293 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (325 : Vertex) [(257 : Vertex), (293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 76 = true := by
  rw [value76, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (293 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 94 = true := by
  rw [value75, value76, value77, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ∈ [(261 : Vertex), (295 : Vertex), (357 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (293 : Vertex) [(261 : Vertex), (295 : Vertex), (357 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 94 = false := by
  rw [value75, value76, value77, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (261 : Vertex) (295 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 77 = true ∨ valuation q 94 = true := by
  rw [value76, value77, value94, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(295 : Vertex), (357 : Vertex)] := by decide
  have hg := other_cover q (293 : Vertex) (261 : Vertex) [(295 : Vertex), (357 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 75 = true ∨ valuation q 94 = true := by
  rw [value75, value76, value94, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(261 : Vertex), (357 : Vertex)] := by decide
  have hg := other_cover q (293 : Vertex) (295 : Vertex) [(261 : Vertex), (357 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 75 = true ∨ valuation q 77 = true := by
  rw [value75, value76, value77, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (293 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(261 : Vertex), (295 : Vertex)] := by decide
  have hg := other_cover q (293 : Vertex) (357 : Vertex) [(261 : Vertex), (295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 96 = true := by
  rw [value77, value96, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(359 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (293 : Vertex) [(359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 76 = true := by
  rw [value76, value77, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(293 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (359 : Vertex) [(293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 1 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value1, value74, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (257 : Vertex) (323 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 1 = false ∨ valuation q 74 = false ∨ valuation q 81 = false := by
  rw [value1, value74, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (257 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 1 = false ∨ valuation q 74 = false ∨ valuation q 89 = false := by
  rw [value1, value74, value78, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (257 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 1 = false ∨ valuation q 74 = false ∨ valuation q 103 = false := by
  rw [value1, value74, value78, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (257 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 1 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value1, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (323 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 1 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value1, value78, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (323 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 1 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value1, value78, value81, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value74, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (323 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E260.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112260
