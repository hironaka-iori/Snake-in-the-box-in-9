import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 202 = true ∨ valuation q 77 = true := by
  rw [value75, value77, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (345 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 68 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value68, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (324 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value76, value77, value78, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(341 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (324 : Vertex) [(341 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 68 = true ∨ valuation q 78 = true := by
  rw [value68, value76, value78, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(324 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (341 : Vertex) [(324 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 203 = true ∨ valuation q 68 = true ∨ valuation q 77 = true := by
  rw [value68, value76, value77, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(324 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (342 : Vertex) [(324 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value69, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (337 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 69 = false ∨ valuation q 75 = false ∨ valuation q 79 = false := by
  rw [value69, value75, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (337 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 79 = false := by
  rw [value75, value76, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (337 : Vertex) (340 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 79 = true := by
  rw [value75, value76, value77, value79, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(337 : Vertex), (340 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (325 : Vertex) [(337 : Vertex), (340 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 69 = true ∨ valuation q 76 = true ∨ valuation q 79 = true := by
  rw [value69, value76, value77, value79, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(325 : Vertex), (340 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (337 : Vertex) [(325 : Vertex), (340 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 204 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 79 = true := by
  rw [value69, value75, value77, value79, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(325 : Vertex), (337 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (340 : Vertex) [(325 : Vertex), (337 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 76 = true ∨ valuation q 79 = true := by
  rw [value76, value78, value79, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(340 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (326 : Vertex) [(340 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 70 = true ∨ valuation q 79 = true := by
  rw [value70, value78, value79, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(326 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (340 : Vertex) [(326 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 205 = true ∨ valuation q 70 = true ∨ valuation q 76 = true := by
  rw [value70, value76, value78, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(326 : Vertex), (340 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (343 : Vertex) [(326 : Vertex), (340 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 71 = false := by
  rw [value7, value62, value71, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 77 = false := by
  rw [value7, value62, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 78 = false := by
  rw [value7, value62, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 84 = false := by
  rw [value7, value62, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 122 = false := by
  rw [value7, value62, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value7, value71, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value7, value71, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 71 = false ∨ valuation q 84 = false := by
  rw [value7, value71, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 71 = false ∨ valuation q 122 = false := by
  rw [value7, value71, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value7, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 77 = false ∨ valuation q 84 = false := by
  rw [value7, value77, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (341 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 77 = false ∨ valuation q 122 = false := by
  rw [value7, value77, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (341 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value7, value78, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 78 = false ∨ valuation q 122 = false := by
  rw [value7, value78, value79, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (342 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 7 = false ∨ valuation q 84 = false ∨ valuation q 122 = false := by
  rw [value7, value79, value84, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (351 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value62, value71, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (327 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value62, value71, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 62 = false ∨ valuation q 71 = false ∨ valuation q 84 = false := by
  rw [value62, value71, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (327 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E052.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112052
