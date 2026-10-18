import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value74, value78, value79, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (323 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value74, value78, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (323 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 79 = false ∨ valuation q 103 = false := by
  rw [value74, value78, value79, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (323 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value74, value78, value81, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 81 = false ∨ valuation q 103 = false := by
  rw [value74, value78, value81, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (325 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value74, value78, value85, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (329 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 85 = false ∨ valuation q 103 = false := by
  rw [value74, value78, value85, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (329 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 89 = false ∨ valuation q 103 = false := by
  rw [value74, value78, value89, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (257 : Vertex) (337 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value78, value79, value81, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (323 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 103 = false := by
  rw [value78, value79, value81, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (323 : Vertex) (325 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value78, value79, value85, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (323 : Vertex) (329 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 89 = false ∨ valuation q 103 = false := by
  rw [value78, value79, value89, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (323 : Vertex) (337 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 89 = false ∨ valuation q 103 = false := by
  rw [value78, value81, value89, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (325 : Vertex) (337 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 74 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 103 = true := by
  rw [value74, value78, value79, value81, value85, value89, value103, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(257 : Vertex), (323 : Vertex), (325 : Vertex), (329 : Vertex), (337 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (65 : Vertex) [(257 : Vertex), (323 : Vertex), (325 : Vertex), (329 : Vertex), (337 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 1 = true ∨ valuation q 74 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 89 = true := by
  rw [value1, value74, value78, value79, value81, value85, value89, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(65 : Vertex), (257 : Vertex), (323 : Vertex), (325 : Vertex), (329 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (449 : Vertex) [(65 : Vertex), (257 : Vertex), (323 : Vertex), (325 : Vertex), (329 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 79 = true := by
  rw [value79, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (323 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 93 = true ∨ valuation q 104 = true := by
  rw [value78, value79, value83, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ∈ [(321 : Vertex), (327 : Vertex), (355 : Vertex), (451 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (323 : Vertex) [(321 : Vertex), (327 : Vertex), (355 : Vertex), (451 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 83 = true ∨ valuation q 93 = true ∨ valuation q 104 = true := by
  rw [value79, value83, value93, value104, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(327 : Vertex), (355 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (321 : Vertex) [(327 : Vertex), (355 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 104 = true := by
  rw [value78, value79, value83, value104, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(321 : Vertex), (327 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (355 : Vertex) [(321 : Vertex), (327 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 93 = true := by
  rw [value78, value79, value83, value93, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(321 : Vertex), (327 : Vertex), (355 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (451 : Vertex) [(321 : Vertex), (327 : Vertex), (355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 207 = true ∨ valuation q 81 = true ∨ valuation q 82 = true := by
  rw [value80, value81, value82, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(325 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (452 : Vertex) [(325 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 3 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value3, value75, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (69 : Vertex) (261 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 3 = false ∨ valuation q 75 = false ∨ valuation q 91 = false := by
  rw [value3, value75, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (69 : Vertex) (261 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 87 = false := by
  rw [value75, value78, value81, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 91 = false := by
  rw [value75, value78, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 94 = false := by
  rw [value75, value78, value81, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 106 = false := by
  rw [value75, value78, value81, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value75, value81, value87, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (333 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 87 = false ∨ valuation q 106 = false := by
  rw [value75, value81, value87, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (333 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value75, value81, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (341 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 106 = false := by
  rw [value75, value81, value91, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (341 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 78 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value78, value81, value87, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (321 : Vertex) (333 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E260.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112260
