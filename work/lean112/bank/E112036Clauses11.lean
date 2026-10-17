import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 5 = true ∨ valuation q 77 = true ∨ valuation q 94 = true := by
  rw [value5, value72, value77, value94, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(39 : Vertex), (303 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (294 : Vertex) [(39 : Vertex), (303 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 5 = true ∨ valuation q 71 = true ∨ valuation q 94 = true := by
  rw [value5, value71, value72, value94, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(39 : Vertex), (294 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (303 : Vertex) [(39 : Vertex), (294 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 5 = true ∨ valuation q 71 = true ∨ valuation q 77 = true := by
  rw [value5, value71, value72, value77, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(39 : Vertex), (294 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (423 : Vertex) [(39 : Vertex), (294 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 6 = false ∨ valuation q 69 = false ∨ valuation q 95 = false := by
  rw [value6, value69, value73, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 69 = true ∨ valuation q 74 = true ∨ valuation q 95 = true := by
  rw [value69, value73, value74, value95, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(288 : Vertex), (297 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (40 : Vertex) [(288 : Vertex), (297 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 6 = true ∨ valuation q 74 = true ∨ valuation q 95 = true := by
  rw [value6, value73, value74, value95, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(40 : Vertex), (297 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(40 : Vertex), (297 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 6 = true ∨ valuation q 69 = true ∨ valuation q 95 = true := by
  rw [value6, value69, value73, value95, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(40 : Vertex), (288 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (297 : Vertex) [(40 : Vertex), (288 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 6 = true ∨ valuation q 69 = true ∨ valuation q 74 = true := by
  rw [value6, value69, value73, value74, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(40 : Vertex), (288 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (424 : Vertex) [(40 : Vertex), (288 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value7, value70, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (289 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 70 = false ∨ valuation q 75 = false := by
  rw [value7, value70, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (289 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 70 = false ∨ valuation q 76 = false := by
  rw [value7, value70, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (289 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value7, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (296 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value7, value73, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (296 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value7, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (41 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value70, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (296 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value70, value73, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (296 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 70 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value70, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value73, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (296 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 203 = true ∨ valuation q 77 = true ∨ valuation q 97 = true := by
  rw [value75, value77, value97, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(303 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (297 : Vertex) [(303 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 203 = true ∨ valuation q 74 = true ∨ valuation q 97 = true := by
  rw [value74, value75, value97, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(297 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (303 : Vertex) [(297 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 203 = true ∨ valuation q 74 = true ∨ valuation q 77 = true := by
  rw [value74, value75, value77, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(297 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (427 : Vertex) [(297 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 85 = false := by
  rw [value74, value76, value77, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (301 : Vertex) (297 : Vertex) (303 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 74 = true ∨ valuation q 77 = true := by
  rw [value74, value76, value77, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(297 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (317 : Vertex) [(297 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 72 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value72, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 72 = false ∨ valuation q 75 = false ∨ valuation q 100 = false := by
  rw [value72, value75, value77, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 72 = false ∨ valuation q 76 = false ∨ valuation q 100 = false := by
  rw [value72, value76, value77, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 100 = false := by
  rw [value75, value76, value77, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (299 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 205 = true ∨ valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 100 = true := by
  rw [value72, value75, value77, value100, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(295 : Vertex), (299 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (301 : Vertex) [(295 : Vertex), (299 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 70 = true ∨ valuation q 80 = true ∨ valuation q 101 = true := by
  rw [value70, value78, value80, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ∈ [(289 : Vertex), (307 : Vertex), (433 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (305 : Vertex) [(289 : Vertex), (307 : Vertex), (433 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 70 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value70, value78, value80, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 206 = true ∨ valuation q 80 = true ∨ valuation q 101 = true := by
  rw [value78, value80, value101, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(307 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (289 : Vertex) [(307 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 206 = true ∨ valuation q 70 = true ∨ valuation q 101 = true := by
  rw [value70, value78, value101, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(289 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(289 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E036.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112036
