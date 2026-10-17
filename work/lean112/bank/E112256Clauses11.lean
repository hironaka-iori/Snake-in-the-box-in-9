import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value16, value53, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (223 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 50 = false ∨ valuation q 72 = false := by
  rw [value48, value50, value53, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (213 : Vertex) (217 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value48, value53, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (213 : Vertex) (223 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value50, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (217 : Vertex) (220 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 72 = false := by
  rw [value50, value52, value53, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (217 : Vertex) (220 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 50 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value50, value53, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (217 : Vertex) (223 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value52, value53, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (220 : Vertex) (223 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 72 = false ∨ valuation q 114 = false := by
  rw [value52, value53, value72, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (220 : Vertex) (253 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 16 = true ∨ valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 114 = true := by
  rw [value16, value48, value50, value52, value53, value54, value114, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (253 : Vertex) → w ∈ [(93 : Vertex), (213 : Vertex), (217 : Vertex), (220 : Vertex), (223 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (253 : Vertex) [(93 : Vertex), (213 : Vertex), (217 : Vertex), (220 : Vertex), (223 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 16 = true ∨ valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 72 = true := by
  rw [value16, value48, value50, value52, value53, value54, value72, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(93 : Vertex), (213 : Vertex), (217 : Vertex), (220 : Vertex), (223 : Vertex), (253 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (477 : Vertex) [(93 : Vertex), (213 : Vertex), (217 : Vertex), (220 : Vertex), (223 : Vertex), (253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 18 = false ∨ valuation q 44 = false ∨ valuation q 49 = false := by
  rw [value18, value44, value49, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (223 : Vertex) (95 : Vertex) (207 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 18 = false ∨ valuation q 44 = false ∨ valuation q 53 = false := by
  rw [value18, value44, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (223 : Vertex) (95 : Vertex) (207 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 18 = false ∨ valuation q 49 = false ∨ valuation q 53 = false := by
  rw [value18, value49, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (223 : Vertex) (95 : Vertex) (215 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 44 = false ∨ valuation q 49 = false ∨ valuation q 53 = false := by
  rw [value44, value49, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (223 : Vertex) (207 : Vertex) (215 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 44 = true ∨ valuation q 49 = true ∨ valuation q 53 = true := by
  rw [value44, value49, value53, value54, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (223 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(207 : Vertex), (215 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (223 : Vertex) (95 : Vertex) [(207 : Vertex), (215 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 18 = true ∨ valuation q 49 = true ∨ valuation q 53 = true := by
  rw [value18, value49, value53, value54, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (223 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(95 : Vertex), (215 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (223 : Vertex) (207 : Vertex) [(95 : Vertex), (215 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 18 = true ∨ valuation q 44 = true ∨ valuation q 53 = true := by
  rw [value18, value44, value53, value54, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (223 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(95 : Vertex), (207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (223 : Vertex) (215 : Vertex) [(95 : Vertex), (207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 19 = false ∨ valuation q 36 = false ∨ valuation q 57 = false := by
  rw [value19, value36, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (192 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 19 = false ∨ valuation q 36 = false ∨ valuation q 63 = false := by
  rw [value19, value36, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (192 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 19 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value19, value55, value57, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (228 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 36 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value36, value55, value57, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (192 : Vertex) (228 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 36 = true ∨ valuation q 57 = true ∨ valuation q 63 = true := by
  rw [value36, value55, value57, value63, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(192 : Vertex), (228 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (96 : Vertex) [(192 : Vertex), (228 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 19 = true ∨ valuation q 57 = true ∨ valuation q 63 = true := by
  rw [value19, value55, value57, value63, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(96 : Vertex), (228 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (192 : Vertex) [(96 : Vertex), (228 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 19 = true ∨ valuation q 36 = true ∨ valuation q 63 = true := by
  rw [value19, value36, value55, value63, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(96 : Vertex), (192 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (228 : Vertex) [(96 : Vertex), (192 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 19 = true ∨ valuation q 36 = true ∨ valuation q 57 = true := by
  rw [value19, value36, value55, value57, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(96 : Vertex), (192 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (240 : Vertex) [(96 : Vertex), (192 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value56, value58, value60, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (231 : Vertex) (235 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 183 = true ∨ valuation q 60 = true ∨ valuation q 65 = true := by
  rw [value56, value60, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(235 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (231 : Vertex) [(235 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 183 = true ∨ valuation q 58 = true ∨ valuation q 65 = true := by
  rw [value56, value58, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(231 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (235 : Vertex) [(231 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 57 = true := by
  rw [value57, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (228 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 39 = true ∨ valuation q 55 = true ∨ valuation q 66 = true := by
  rw [value39, value55, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ∈ [(196 : Vertex), (224 : Vertex), (244 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (228 : Vertex) [(196 : Vertex), (224 : Vertex), (244 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 39 = false ∨ valuation q 55 = false ∨ valuation q 66 = false := by
  rw [value39, value55, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (196 : Vertex) (224 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 39 = false ∨ valuation q 55 = false := by
  rw [value39, value55, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (228 : Vertex) (196 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E256.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112256
