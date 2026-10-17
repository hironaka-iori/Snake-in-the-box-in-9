import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 60 = false ∨ valuation q 65 = false ∨ valuation q 116 = false := by
  rw [value60, value62, value65, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (241 : Vertex) (247 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 60 = false ∨ valuation q 68 = false ∨ valuation q 116 = false := by
  rw [value60, value62, value68, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (241 : Vertex) (251 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value61, value62, value65, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (242 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 116 = false := by
  rw [value61, value62, value65, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (242 : Vertex) (247 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 68 = false ∨ valuation q 116 = false := by
  rw [value61, value62, value68, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (242 : Vertex) (251 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 116 = false := by
  rw [value62, value65, value68, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (247 : Vertex) (251 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 27 = true ∨ valuation q 60 = true ∨ valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 116 = true := by
  rw [value27, value60, value62, value65, value68, value116, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(115 : Vertex), (241 : Vertex), (247 : Vertex), (251 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (242 : Vertex) [(115 : Vertex), (241 : Vertex), (247 : Vertex), (251 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 27 = true ∨ valuation q 60 = true ∨ valuation q 61 = true ∨ valuation q 68 = true ∨ valuation q 116 = true := by
  rw [value27, value60, value61, value62, value68, value116, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(115 : Vertex), (241 : Vertex), (242 : Vertex), (251 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (247 : Vertex) [(115 : Vertex), (241 : Vertex), (242 : Vertex), (251 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 27 = true ∨ valuation q 60 = true ∨ valuation q 61 = true ∨ valuation q 65 = true ∨ valuation q 116 = true := by
  rw [value27, value60, value61, value62, value65, value116, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(115 : Vertex), (241 : Vertex), (242 : Vertex), (247 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (251 : Vertex) [(115 : Vertex), (241 : Vertex), (242 : Vertex), (247 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 53 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value53, value60, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (241 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 53 = false ∨ valuation q 60 = false ∨ valuation q 69 = false := by
  rw [value53, value60, value63, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (241 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 53 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value53, value63, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (247 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 60 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value60, value63, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (241 : Vertex) (247 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 61 = false := by
  rw [value45, value54, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (230 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 65 = false := by
  rw [value45, value54, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (230 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 118 = false := by
  rw [value45, value54, value64, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (230 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 45 = false ∨ valuation q 61 = false ∨ valuation q 65 = false := by
  rw [value45, value61, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (242 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 45 = false ∨ valuation q 61 = false ∨ valuation q 118 = false := by
  rw [value45, value61, value64, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (242 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 45 = false ∨ valuation q 65 = false ∨ valuation q 118 = false := by
  rw [value45, value64, value65, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (247 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 54 = false ∨ valuation q 61 = false ∨ valuation q 65 = false := by
  rw [value54, value61, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (230 : Vertex) (242 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 54 = false ∨ valuation q 61 = false ∨ valuation q 118 = false := by
  rw [value54, value61, value64, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (230 : Vertex) (242 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 54 = false ∨ valuation q 65 = false ∨ valuation q 118 = false := by
  rw [value54, value64, value65, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (230 : Vertex) (247 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 118 = false := by
  rw [value61, value64, value65, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (242 : Vertex) (247 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 45 = true ∨ valuation q 54 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value45, value54, value61, value64, value65, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (246 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(182 : Vertex), (230 : Vertex), (242 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (246 : Vertex) (502 : Vertex) [(182 : Vertex), (230 : Vertex), (242 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value62, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (247 : Vertex) (243 : Vertex) (245 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 70 = false := by
  rw [value63, value64, value65, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (247 : Vertex) (245 : Vertex) (246 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 63 = true ∨ valuation q 64 = true ∨ valuation q 70 = true := by
  rw [value63, value64, value65, value70, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(245 : Vertex), (246 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (243 : Vertex) [(245 : Vertex), (246 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 70 = true := by
  rw [value62, value64, value65, value70, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(243 : Vertex), (246 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(243 : Vertex), (246 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value62, value63, value65, value70, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(243 : Vertex), (245 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (246 : Vertex) [(243 : Vertex), (245 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 64 = true := by
  rw [value62, value63, value64, value65, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(243 : Vertex), (245 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (255 : Vertex) [(243 : Vertex), (245 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 46 = false ∨ valuation q 55 = false ∨ valuation q 119 = false := by
  rw [value46, value55, value66, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (184 : Vertex) (232 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 55 = true ∨ valuation q 67 = true ∨ valuation q 119 = true := by
  rw [value55, value66, value67, value119, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(232 : Vertex), (249 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [(232 : Vertex), (249 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E020.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112020
