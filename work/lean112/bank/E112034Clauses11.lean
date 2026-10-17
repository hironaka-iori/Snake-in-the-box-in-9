import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 78 = true ∨ valuation q 119 = true := by
  rw [value78, value79, value119, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (369 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(368 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (369 : Vertex) (371 : Vertex) [(368 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 78 = true ∨ valuation q 80 = true := by
  rw [value78, value79, value80, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (369 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(368 : Vertex), (371 : Vertex)] := by decide
  have hg := other_cover q (369 : Vertex) (497 : Vertex) [(368 : Vertex), (371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 70 = false ∨ valuation q 79 = false ∨ valuation q 120 = false := by
  rw [value70, value79, value80, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (355 : Vertex) (369 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 70 = false ∨ valuation q 79 = false := by
  rw [value70, value79, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (371 : Vertex) (355 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 208 = true ∨ valuation q 79 = true ∨ valuation q 120 = true := by
  rw [value79, value80, value120, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(369 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (355 : Vertex) [(369 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 208 = true ∨ valuation q 70 = true ∨ valuation q 120 = true := by
  rw [value70, value80, value120, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (369 : Vertex) → w ∈ [(355 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (369 : Vertex) [(355 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value71, value78, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (356 : Vertex) (368 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 209 = true ∨ valuation q 71 = true ∨ valuation q 83 = true := by
  rw [value71, value81, value83, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(356 : Vertex), (380 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (368 : Vertex) [(356 : Vertex), (380 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 209 = true ∨ valuation q 71 = true ∨ valuation q 78 = true := by
  rw [value71, value78, value81, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(356 : Vertex), (368 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (380 : Vertex) [(356 : Vertex), (368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 64 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value64, value78, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (312 : Vertex) (368 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 64 = false ∨ valuation q 83 = false ∨ valuation q 124 = false := by
  rw [value64, value82, value83, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (312 : Vertex) (380 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 124 = false := by
  rw [value78, value82, value83, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (368 : Vertex) (380 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value81, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (380 : Vertex) (372 : Vertex) (376 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 211 = true ∨ valuation q 81 = true ∨ valuation q 82 = true := by
  rw [value81, value82, value83, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (382 : Vertex) → w ∈ [(372 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (382 : Vertex) [(372 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 85 = true := by
  rw [value84, value85, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(383 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (380 : Vertex) [(383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 212 = true ∨ valuation q 83 = true := by
  rw [value83, value84, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(380 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (383 : Vertex) [(380 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 68 = false ∨ valuation q 77 = false ∨ valuation q 84 = false := by
  rw [value68, value77, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (319 : Vertex) (367 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 213 = true ∨ valuation q 68 = true ∨ valuation q 84 = true := by
  rw [value68, value84, value85, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(319 : Vertex), (382 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (367 : Vertex) [(319 : Vertex), (382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 213 = true ∨ valuation q 68 = true ∨ valuation q 77 = true := by
  rw [value68, value77, value85, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (382 : Vertex) → w ∈ [(319 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (382 : Vertex) [(319 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 14 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value14, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 14 = false ∨ valuation q 87 = false ∨ valuation q 96 = false := by
  rw [value14, value86, value87, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 14 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value14, value86, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (418 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 14 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value14, value86, value88, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (418 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 50 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value50, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 50 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value50, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 50 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value50, value86, value88, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (418 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value86, value87, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (418 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 106 = false := by
  rw [value86, value87, value88, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (418 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 106 = false := by
  rw [value86, value87, value90, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (420 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 96 = false ∨ valuation q 106 = false := by
  rw [value86, value87, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (432 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 96 = false := by
  rw [value86, value88, value90, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (418 : Vertex) (420 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 106 = false := by
  rw [value86, value88, value90, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (418 : Vertex) (420 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E034.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112034
