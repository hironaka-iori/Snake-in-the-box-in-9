import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 59 = false := by
  rw [value26, value44, value59, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (141 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 62 = false := by
  rw [value26, value44, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (141 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 66 = false := by
  rw [value26, value44, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (141 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 26 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value26, value59, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (165 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 26 = false ∨ valuation q 59 = false ∨ valuation q 66 = false := by
  rw [value26, value59, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (165 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 26 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value26, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (169 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 26 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value26, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (169 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 26 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value26, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (172 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 44 = false ∨ valuation q 59 = false ∨ valuation q 62 = false := by
  rw [value44, value59, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (141 : Vertex) (165 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 44 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value44, value59, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (141 : Vertex) (165 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 44 = false ∨ valuation q 59 = false ∨ valuation q 66 = false := by
  rw [value44, value59, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (141 : Vertex) (165 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 44 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value44, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (141 : Vertex) (169 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 44 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value44, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (141 : Vertex) (169 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 44 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value44, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (141 : Vertex) (172 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value59, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (165 : Vertex) (169 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value59, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (165 : Vertex) (169 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value59, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (165 : Vertex) (172 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value62, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (169 : Vertex) (172 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 181 = true ∨ valuation q 26 = true ∨ valuation q 44 = true ∨ valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 108 = true := by
  rw [value26, value44, value62, value64, value65, value66, value108, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(45 : Vertex), (141 : Vertex), (169 : Vertex), (172 : Vertex), (175 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (165 : Vertex) [(45 : Vertex), (141 : Vertex), (169 : Vertex), (172 : Vertex), (175 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 65 = true ∨ valuation q 77 = true := by
  rw [value65, value66, value77, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (47 : Vertex) → w ∈ [(173 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (47 : Vertex) [(173 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 27 = true ∨ valuation q 77 = true := by
  rw [value27, value66, value77, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(47 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (173 : Vertex) [(47 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 182 = true ∨ valuation q 27 = true ∨ valuation q 65 = true := by
  rw [value27, value65, value66, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (191 : Vertex) → w ∈ [(47 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (191 : Vertex) [(47 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 28 = false ∨ valuation q 46 = false ∨ valuation q 68 = false := by
  rw [value28, value46, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (144 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 28 = false ∨ valuation q 46 = false ∨ valuation q 70 = false := by
  rw [value28, value46, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (144 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 28 = false ∨ valuation q 46 = false ∨ valuation q 72 = false := by
  rw [value28, value46, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (144 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 28 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value28, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 28 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value28, value67, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 46 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value46, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (144 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 46 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value46, value67, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (144 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 46 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value46, value67, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (144 : Vertex) (180 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 183 = true ∨ valuation q 46 = true ∨ valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 72 = true := by
  rw [value46, value67, value68, value70, value72, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(144 : Vertex), (178 : Vertex), (180 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (48 : Vertex) [(144 : Vertex), (178 : Vertex), (180 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 183 = true ∨ valuation q 28 = true ∨ valuation q 46 = true ∨ valuation q 70 = true ∨ valuation q 72 = true := by
  rw [value28, value46, value67, value70, value72, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(48 : Vertex), (144 : Vertex), (180 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (178 : Vertex) [(48 : Vertex), (144 : Vertex), (180 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E257.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112257
