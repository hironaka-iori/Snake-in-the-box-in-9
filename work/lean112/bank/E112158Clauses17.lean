import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 189 = true ∨ valuation q 60 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 69 = true := by
  rw [value60, value66, value67, value69, value71, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (223 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(207 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (223 : Vertex) (222 : Vertex) [(207 : Vertex), (215 : Vertex), (219 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 73 = true := by
  rw [value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ∈ [(261 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (257 : Vertex) [(261 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 190 = true := by
  rw [value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 1 = false ∨ valuation q 75 = false ∨ valuation q 88 = false := by
  rw [value1, value73, value75, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 88 = true := by
  rw [value72, value73, value75, value88, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(257 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (5 : Vertex) [(257 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 1 = true ∨ valuation q 72 = true ∨ valuation q 88 = true := by
  rw [value1, value72, value73, value88, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(5 : Vertex), (257 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (325 : Vertex) [(5 : Vertex), (257 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 1 = true ∨ valuation q 72 = true ∨ valuation q 75 = true := by
  rw [value1, value72, value73, value75, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(5 : Vertex), (257 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (389 : Vertex) [(5 : Vertex), (257 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 2 = false ∨ valuation q 76 = false ∨ valuation q 91 = false := by
  rw [value2, value74, value76, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (12 : Vertex) (332 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 192 = true ∨ valuation q 76 = true ∨ valuation q 91 = true := by
  rw [value74, value76, value91, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(332 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (12 : Vertex) [(332 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 192 = true ∨ valuation q 2 = true ∨ valuation q 91 = true := by
  rw [value2, value74, value91, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(12 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (332 : Vertex) [(12 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 193 = true ∨ valuation q 77 = true := by
  rw [value75, value77, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (261 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 193 = true ∨ valuation q 73 = true := by
  rw [value73, value75, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(261 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (333 : Vertex) [(261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 82 = false := by
  rw [value74, value76, value77, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (333 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 77 = true ∨ valuation q 82 = true := by
  rw [value76, value77, value82, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(333 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (268 : Vertex) [(333 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 74 = true ∨ valuation q 77 = true := by
  rw [value74, value76, value77, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(268 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (348 : Vertex) [(268 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 76 = true := by
  rw [value76, value77, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(332 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (325 : Vertex) [(332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 195 = true ∨ valuation q 75 = true := by
  rw [value75, value77, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(325 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (332 : Vertex) [(325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = true := by
  rw [value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ∈ [(337 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (336 : Vertex) [(337 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 78 = true := by
  rw [value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 197 = true ∨ valuation q 80 = true := by
  rw [value79, value80, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (336 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 198 = true ∨ valuation q 81 = true := by
  rw [value80, value81, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 24 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value24, value80, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (339 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 199 = true ∨ valuation q 24 = true ∨ valuation q 84 = true := by
  rw [value24, value81, value84, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(87 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (339 : Vertex) [(87 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 200 = true ∨ valuation q 83 = true := by
  rw [value82, value83, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (332 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 200 = true ∨ valuation q 76 = true := by
  rw [value76, value82, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(332 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 201 = true ∨ valuation q 84 = true := by
  rw [value83, value84, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(351 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 201 = true ∨ valuation q 82 = true := by
  rw [value82, value83, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (351 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 83 = true := by
  rw [value83, value84, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (343 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 202 = true ∨ valuation q 81 = true := by
  rw [value81, value84, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (351 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (351 : Vertex) (350 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value85, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 93 = false := by
  rw [value85, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value85, value86, value89, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E158.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112158
