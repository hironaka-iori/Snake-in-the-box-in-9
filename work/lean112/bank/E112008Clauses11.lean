import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 22 = true ∨ valuation q 58 = true ∨ valuation q 59 = true := by
  rw [value22, value56, value58, value59, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(105 : Vertex), (235 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (489 : Vertex) [(105 : Vertex), (235 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 23 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value23, value39, value52, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (170 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 23 = false ∨ valuation q 39 = false ∨ valuation q 58 = false := by
  rw [value23, value39, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (170 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 39 = false ∨ valuation q 52 = false ∨ valuation q 58 = false := by
  rw [value39, value52, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (170 : Vertex) (226 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 39 = true ∨ valuation q 52 = true ∨ valuation q 58 = true := by
  rw [value39, value52, value57, value58, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(170 : Vertex), (226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (106 : Vertex) [(170 : Vertex), (226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 23 = true ∨ valuation q 52 = true ∨ valuation q 58 = true := by
  rw [value23, value52, value57, value58, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(106 : Vertex), (226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (170 : Vertex) [(106 : Vertex), (226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 23 = true ∨ valuation q 39 = true ∨ valuation q 58 = true := by
  rw [value23, value39, value57, value58, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(106 : Vertex), (170 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (226 : Vertex) [(106 : Vertex), (170 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 23 = true ∨ valuation q 39 = true ∨ valuation q 52 = true := by
  rw [value23, value39, value52, value57, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(106 : Vertex), (170 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (235 : Vertex) [(106 : Vertex), (170 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 58 = true := by
  rw [value58, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (235 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value40, value53, value56, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 53 = false ∨ valuation q 57 = false := by
  rw [value40, value53, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 53 = false ∨ valuation q 60 = false := by
  rw [value40, value53, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (227 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value40, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (233 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value40, value56, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (233 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value40, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value53, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (233 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value53, value56, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (233 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 53 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value53, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value56, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (233 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 40 = false ∨ valuation q 60 = false := by
  rw [value40, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (235 : Vertex) (171 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 53 = false ∨ valuation q 60 = false := by
  rw [value53, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (235 : Vertex) (227 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value57, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (235 : Vertex) (234 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 182 = true ∨ valuation q 40 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 57 = true := by
  rw [value40, value53, value56, value57, value58, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(171 : Vertex), (227 : Vertex), (233 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (239 : Vertex) [(171 : Vertex), (227 : Vertex), (233 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 59 = true := by
  rw [value59, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (237 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value54, value56, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (229 : Vertex) (233 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value56, value60, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (237 : Vertex) (233 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 56 = true ∨ valuation q 60 = true := by
  rw [value56, value59, value60, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(233 : Vertex), (239 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (229 : Vertex) [(233 : Vertex), (239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 54 = true ∨ valuation q 60 = true := by
  rw [value54, value59, value60, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(229 : Vertex), (239 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (233 : Vertex) [(229 : Vertex), (239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 54 = true ∨ valuation q 56 = true := by
  rw [value54, value56, value59, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(229 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (239 : Vertex) [(229 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 69 = false := by
  rw [value55, value58, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (231 : Vertex) (235 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 55 = false ∨ valuation q 59 = false ∨ valuation q 69 = false := by
  rw [value55, value59, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (231 : Vertex) (237 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 69 = false := by
  rw [value58, value59, value60, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (235 : Vertex) (237 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E008.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112008
