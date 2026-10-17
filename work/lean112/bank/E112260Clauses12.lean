import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 42 = true ∨ valuation q 49 = true := by
  rw [value42, value49, value53, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(202 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (90 : Vertex) [(202 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 16 = true ∨ valuation q 49 = true := by
  rw [value16, value49, value53, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(90 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (202 : Vertex) [(90 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 16 = true ∨ valuation q 42 = true := by
  rw [value16, value42, value53, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(90 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (210 : Vertex) [(90 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 44 = false ∨ valuation q 50 = false ∨ valuation q 72 = false := by
  rw [value44, value50, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (204 : Vertex) (212 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 50 = true ∨ valuation q 72 = true := by
  rw [value50, value54, value72, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(212 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (204 : Vertex) [(212 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 44 = true ∨ valuation q 50 = true := by
  rw [value44, value50, value54, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(204 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (252 : Vertex) [(204 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 36 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value36, value55, value56, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (192 : Vertex) (226 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 56 = true ∨ valuation q 60 = true := by
  rw [value55, value56, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(226 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (192 : Vertex) [(226 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 36 = true ∨ valuation q 60 = true := by
  rw [value36, value55, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(192 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (226 : Vertex) [(192 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 36 = true ∨ valuation q 56 = true := by
  rw [value36, value55, value56, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(192 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (232 : Vertex) [(192 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value19, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (224 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value19, value55, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (224 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 66 = false := by
  rw [value19, value55, value56, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (224 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 116 = false := by
  rw [value19, value55, value56, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (224 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value19, value56, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (227 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 57 = false ∨ valuation q 66 = false := by
  rw [value19, value56, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (227 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 57 = false ∨ valuation q 116 = false := by
  rw [value19, value56, value57, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (227 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 59 = false ∨ valuation q 66 = false := by
  rw [value19, value56, value59, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (98 : Vertex) (230 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 38 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value38, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (194 : Vertex) (224 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 38 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value38, value55, value56, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (194 : Vertex) (224 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 38 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value38, value56, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (194 : Vertex) (227 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 38 = false ∨ valuation q 59 = false ∨ valuation q 66 = false := by
  rw [value38, value56, value59, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (194 : Vertex) (230 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value55, value56, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (224 : Vertex) (227 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 183 = true ∨ valuation q 19 = true ∨ valuation q 38 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 59 = true ∨ valuation q 66 = true := by
  rw [value19, value38, value55, value56, value57, value59, value66, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(98 : Vertex), (194 : Vertex), (224 : Vertex), (227 : Vertex), (230 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (482 : Vertex) [(98 : Vertex), (194 : Vertex), (224 : Vertex), (227 : Vertex), (230 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 62 = false ∨ valuation q 67 = false := by
  rw [value56, value57, value62, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (226 : Vertex) (235 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 67 = false ∨ valuation q 117 = false := by
  rw [value56, value57, value67, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (226 : Vertex) (243 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 117 = false := by
  rw [value57, value62, value67, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (235 : Vertex) (243 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 184 = true ∨ valuation q 56 = true ∨ valuation q 62 = true ∨ valuation q 117 = true := by
  rw [value56, value57, value62, value117, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (243 : Vertex) [(226 : Vertex), (235 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 20 = false ∨ valuation q 40 = false ∨ valuation q 64 = false := by
  rw [value20, value40, value58, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (197 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 20 = false ∨ valuation q 40 = false ∨ valuation q 68 = false := by
  rw [value20, value40, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (197 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 20 = false ∨ valuation q 64 = false ∨ valuation q 68 = false := by
  rw [value20, value58, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (237 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 40 = false ∨ valuation q 64 = false ∨ valuation q 68 = false := by
  rw [value40, value58, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (197 : Vertex) (237 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E260.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112260
