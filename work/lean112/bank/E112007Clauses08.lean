import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 76 = false := by
  rw [value64, value68, value69, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 64 = false ∨ valuation q 76 = false ∨ valuation q 105 = false := by
  rw [value64, value69, value76, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (345 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 76 = false ∨ valuation q 105 = false := by
  rw [value68, value69, value76, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (328 : Vertex) (345 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value52, value65, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (322 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value52, value65, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (322 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 65 = false ∨ valuation q 77 = false := by
  rw [value52, value65, value70, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (322 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 65 = false ∨ valuation q 106 = false := by
  rw [value52, value65, value70, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (322 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value52, value68, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (328 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 77 = false := by
  rw [value52, value68, value70, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (328 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 106 = false := by
  rw [value52, value68, value70, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (328 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 72 = false ∨ valuation q 77 = false := by
  rw [value52, value70, value72, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (334 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 72 = false ∨ valuation q 106 = false := by
  rw [value52, value70, value72, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (334 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 77 = false ∨ valuation q 106 = false := by
  rw [value52, value70, value77, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (346 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value65, value68, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (328 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 77 = false := by
  rw [value65, value68, value70, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (328 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 106 = false := by
  rw [value65, value68, value70, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (328 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 72 = false ∨ valuation q 77 = false := by
  rw [value65, value70, value72, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (334 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 72 = false ∨ valuation q 106 = false := by
  rw [value65, value70, value72, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (334 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 77 = false ∨ valuation q 106 = false := by
  rw [value65, value70, value77, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (346 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 77 = false := by
  rw [value68, value70, value72, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (328 : Vertex) (334 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 106 = false := by
  rw [value68, value70, value72, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (328 : Vertex) (334 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 77 = false ∨ valuation q 106 = false := by
  rw [value68, value70, value77, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (328 : Vertex) (346 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 77 = false ∨ valuation q 106 = false := by
  rw [value70, value72, value77, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (334 : Vertex) (346 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 188 = true ∨ valuation q 52 = true ∨ valuation q 68 = true ∨ valuation q 72 = true ∨ valuation q 77 = true ∨ valuation q 106 = true := by
  rw [value52, value68, value70, value72, value77, value106, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(266 : Vertex), (328 : Vertex), (334 : Vertex), (346 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (322 : Vertex) [(266 : Vertex), (328 : Vertex), (334 : Vertex), (346 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 188 = true ∨ valuation q 52 = true ∨ valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 77 = true ∨ valuation q 106 = true := by
  rw [value52, value65, value68, value70, value77, value106, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(266 : Vertex), (322 : Vertex), (328 : Vertex), (346 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (334 : Vertex) [(266 : Vertex), (322 : Vertex), (328 : Vertex), (346 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 189 = true ∨ valuation q 72 = true := by
  rw [value71, value72, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(334 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (328 : Vertex) [(334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 189 = true ∨ valuation q 68 = true := by
  rw [value68, value71, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(328 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (334 : Vertex) [(328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 66 = true ∨ valuation q 70 = true ∨ valuation q 71 = true := by
  rw [value66, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ∈ [(326 : Vertex), (330 : Vertex), (332 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (334 : Vertex) [(326 : Vertex), (330 : Vertex), (332 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 190 = true ∨ valuation q 70 = true ∨ valuation q 71 = true := by
  rw [value70, value71, value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (326 : Vertex) [(330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 190 = true ∨ valuation q 66 = true ∨ valuation q 71 = true := by
  rw [value66, value71, value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(326 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (330 : Vertex) [(326 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 190 = true ∨ valuation q 66 = true ∨ valuation q 70 = true := by
  rw [value66, value70, value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(326 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (332 : Vertex) [(326 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 12 = false ∨ valuation q 55 = false ∨ valuation q 77 = false := by
  rw [value12, value55, value73, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (338 : Vertex) (82 : Vertex) (274 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E007.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112007
