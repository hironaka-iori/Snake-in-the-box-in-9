import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 43 = false ∨ valuation q 54 = false := by
  rw [value16, value43, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (175 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 43 = false ∨ valuation q 55 = false := by
  rw [value16, value43, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (175 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 43 = false ∨ valuation q 74 = false := by
  rw [value16, value43, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (175 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 49 = false ∨ valuation q 54 = false := by
  rw [value16, value49, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (183 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value16, value49, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (183 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 49 = false ∨ valuation q 74 = false := by
  rw [value16, value49, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (183 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 16 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value16, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (63 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 43 = false ∨ valuation q 49 = false ∨ valuation q 74 = false := by
  rw [value43, value49, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (183 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 43 = false ∨ valuation q 55 = false ∨ valuation q 74 = false := by
  rw [value43, value55, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 49 = false ∨ valuation q 54 = false ∨ valuation q 74 = false := by
  rw [value49, value54, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (183 : Vertex) (189 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 74 = false := by
  rw [value54, value55, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 176 = true ∨ valuation q 16 = true ∨ valuation q 49 = true ∨ valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 74 = true := by
  rw [value16, value49, value54, value55, value56, value74, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (191 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(63 : Vertex), (183 : Vertex), (189 : Vertex), (190 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (191 : Vertex) (175 : Vertex) [(63 : Vertex), (183 : Vertex), (189 : Vertex), (190 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 176 = true ∨ valuation q 16 = true ∨ valuation q 43 = true ∨ valuation q 49 = true ∨ valuation q 54 = true ∨ valuation q 74 = true := by
  rw [value16, value43, value49, value54, value56, value74, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (191 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(63 : Vertex), (175 : Vertex), (183 : Vertex), (189 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (191 : Vertex) (190 : Vertex) [(63 : Vertex), (175 : Vertex), (183 : Vertex), (189 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 176 = true ∨ valuation q 16 = true ∨ valuation q 43 = true ∨ valuation q 49 = true ∨ valuation q 54 = true ∨ valuation q 55 = true := by
  rw [value16, value43, value49, value54, value55, value56, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (191 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(63 : Vertex), (175 : Vertex), (183 : Vertex), (189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (191 : Vertex) (255 : Vertex) [(63 : Vertex), (175 : Vertex), (183 : Vertex), (189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 36 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value36, value57, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (230 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 36 = false ∨ valuation q 60 = false ∨ valuation q 106 = false := by
  rw [value36, value57, value60, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (230 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 36 = false ∨ valuation q 62 = false ∨ valuation q 106 = false := by
  rw [value36, value57, value62, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (234 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 106 = false := by
  rw [value57, value60, value62, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (230 : Vertex) (234 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value58, value59, value60, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value59, value60, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 178 = true ∨ valuation q 60 = true ∨ valuation q 64 = true := by
  rw [value58, value60, value64, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(230 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (229 : Vertex) [(230 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 178 = true ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value58, value59, value64, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(229 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (230 : Vertex) [(229 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 178 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value58, value59, value60, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(229 : Vertex), (230 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (236 : Vertex) [(229 : Vertex), (230 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 179 = true ∨ valuation q 69 = true := by
  rw [value59, value69, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(245 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (228 : Vertex) [(245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 179 = true ∨ valuation q 58 = true := by
  rw [value58, value59, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(228 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (245 : Vertex) [(228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 65 = false := by
  rw [value57, value58, value60, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (226 : Vertex) (228 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 180 = true ∨ valuation q 57 = true ∨ valuation q 65 = true := by
  rw [value57, value60, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(226 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (228 : Vertex) [(226 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 180 = true ∨ valuation q 57 = true ∨ valuation q 58 = true := by
  rw [value57, value58, value60, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(226 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (238 : Vertex) [(226 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 39 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value39, value61, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (169 : Vertex) (235 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 181 = true ∨ valuation q 63 = true ∨ valuation q 72 = true := by
  rw [value61, value63, value72, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (169 : Vertex) [(235 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 181 = true ∨ valuation q 39 = true ∨ valuation q 72 = true := by
  rw [value39, value61, value72, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(169 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (235 : Vertex) [(169 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 181 = true ∨ valuation q 39 = true ∨ valuation q 63 = true := by
  rw [value39, value61, value63, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(169 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (249 : Vertex) [(169 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E004.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112004
