import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 53 = false ∨ valuation q 90 = false := by
  rw [value53, value90, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (395 : Vertex) (267 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 202 = true ∨ valuation q 87 = true ∨ valuation q 90 = true := by
  rw [value87, value88, value90, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(393 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (267 : Vertex) [(393 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 202 = true ∨ valuation q 53 = true ∨ valuation q 90 = true := by
  rw [value53, value88, value90, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(267 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (393 : Vertex) [(267 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 202 = true ∨ valuation q 53 = true ∨ valuation q 87 = true := by
  rw [value53, value87, value88, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(267 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (399 : Vertex) [(267 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 203 = true ∨ valuation q 87 = true ∨ valuation q 97 = true := by
  rw [value87, value89, value97, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(393 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (399 : Vertex) [(393 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 203 = true ∨ valuation q 87 = true ∨ valuation q 90 = true := by
  rw [value87, value89, value90, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(393 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(393 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 56 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value56, value85, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (391 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 56 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value56, value85, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 56 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value56, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (395 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value85, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (391 : Vertex) (395 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 204 = true ∨ valuation q 56 = true ∨ valuation q 88 = true ∨ valuation q 89 = true := by
  rw [value56, value88, value89, value90, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(271 : Vertex), (395 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(271 : Vertex), (395 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 204 = true ∨ valuation q 56 = true ∨ valuation q 85 = true ∨ valuation q 88 = true := by
  rw [value56, value85, value88, value90, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(271 : Vertex), (391 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (397 : Vertex) [(271 : Vertex), (391 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 57 = false ∨ valuation q 83 = false ∨ valuation q 93 = false := by
  rw [value57, value83, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (385 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 205 = true ∨ valuation q 57 = true ∨ valuation q 83 = true := by
  rw [value57, value83, value91, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(273 : Vertex), (385 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(273 : Vertex), (385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value92, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (403 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 206 = true ∨ valuation q 94 = true ∨ valuation q 95 = true := by
  rw [value92, value94, value95, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(406 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (403 : Vertex) [(406 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = true ∨ valuation q 92 = true := by
  rw [value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ∈ [(401 : Vertex), (402 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (403 : Vertex) [(401 : Vertex), (402 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 207 = true ∨ valuation q 92 = true := by
  rw [value92, value93, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 207 = true ∨ valuation q 91 = true := by
  rw [value91, value93, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(401 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (402 : Vertex) [(401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 208 = true ∨ valuation q 84 = true ∨ valuation q 98 = true := by
  rw [value84, value94, value98, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(390 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (402 : Vertex) [(390 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 210 = true ∨ valuation q 98 = true := by
  rw [value96, value98, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (413 : Vertex) [(414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value94, value95, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 213 = true ∨ valuation q 103 = true := by
  rw [value99, value103, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 214 = true ∨ valuation q 99 = true ∨ valuation q 107 = true := by
  rw [value99, value100, value107, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(480 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (489 : Vertex) [(480 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 214 = true ∨ valuation q 99 = true ∨ valuation q 104 = true := by
  rw [value99, value100, value104, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (497 : Vertex) [(480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 40 = false ∨ valuation q 102 = false ∨ valuation q 110 = false := by
  rw [value40, value101, value102, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 216 = true ∨ valuation q 106 = true := by
  rw [value102, value106, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 216 = true ∨ valuation q 101 = true := by
  rw [value101, value102, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 217 = true ∨ valuation q 41 = true ∨ valuation q 104 = true := by
  rw [value41, value103, value104, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(232 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(232 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value100, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 113 = false := by
  rw [value104, value105, value106, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (489 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 221 = true ∨ valuation q 109 = true := by
  rw [value107, value109, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (481 : Vertex) [(499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E171.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112171
