import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = true ∨ valuation q 56 = true ∨ valuation q 117 = true := by
  rw [value49, value55, value56, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ∈ [(210 : Vertex), (219 : Vertex), (474 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (218 : Vertex) [(210 : Vertex), (219 : Vertex), (474 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 117 = false := by
  rw [value49, value55, value56, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (210 : Vertex) (219 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 176 = true ∨ valuation q 56 = true ∨ valuation q 117 = true := by
  rw [value55, value56, value117, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(219 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (210 : Vertex) [(219 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 176 = true ∨ valuation q 49 = true ∨ valuation q 117 = true := by
  rw [value49, value55, value117, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(210 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (219 : Vertex) [(210 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 176 = true ∨ valuation q 49 = true ∨ valuation q 56 = true := by
  rw [value49, value55, value56, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(210 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (474 : Vertex) [(210 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value46, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 118 = false := by
  rw [value46, value54, value56, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (217 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 46 = false ∨ valuation q 55 = false ∨ valuation q 118 = false := by
  rw [value46, value55, value56, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (218 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 118 = false := by
  rw [value54, value55, value56, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (217 : Vertex) (218 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 177 = true ∨ valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 118 = true := by
  rw [value54, value55, value56, value118, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(217 : Vertex), (218 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (203 : Vertex) [(217 : Vertex), (218 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 177 = true ∨ valuation q 46 = true ∨ valuation q 55 = true ∨ valuation q 118 = true := by
  rw [value46, value55, value56, value118, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(203 : Vertex), (218 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (217 : Vertex) [(203 : Vertex), (218 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 177 = true ∨ valuation q 46 = true ∨ valuation q 54 = true ∨ valuation q 118 = true := by
  rw [value46, value54, value56, value118, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(203 : Vertex), (217 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (218 : Vertex) [(203 : Vertex), (217 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 178 = true ∨ valuation q 54 = true := by
  rw [value54, value57, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (213 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 178 = true ∨ valuation q 51 = true := by
  rw [value51, value57, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(213 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (217 : Vertex) [(213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 3 = false ∨ valuation q 59 = false ∨ valuation q 86 = false := by
  rw [value3, value58, value59, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (10 : Vertex) (282 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 3 = false ∨ valuation q 59 = false := by
  rw [value3, value59, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (266 : Vertex) (10 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 59 = false ∨ valuation q 86 = false := by
  rw [value59, value86, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (266 : Vertex) (282 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 179 = true ∨ valuation q 59 = true ∨ valuation q 86 = true := by
  rw [value58, value59, value86, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(282 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (10 : Vertex) [(282 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 179 = true ∨ valuation q 3 = true ∨ valuation q 86 = true := by
  rw [value3, value58, value86, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(10 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (282 : Vertex) [(10 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 179 = true ∨ valuation q 3 = true ∨ valuation q 59 = true := by
  rw [value3, value58, value59, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(10 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (394 : Vertex) [(10 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 76 = false := by
  rw [value58, value59, value61, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (286 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 180 = true ∨ valuation q 58 = true ∨ valuation q 76 = true := by
  rw [value58, value59, value76, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(266 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (286 : Vertex) [(266 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = true := by
  rw [value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ∈ [(286 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (284 : Vertex) [(286 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 60 = true := by
  rw [value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value59, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (286 : Vertex) (282 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 182 = true ∨ valuation q 59 = true := by
  rw [value59, value61, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(282 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (284 : Vertex) [(282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value62, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (324 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 99 = false := by
  rw [value62, value63, value64, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (324 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 99 = false := by
  rw [value62, value63, value66, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 99 = false := by
  rw [value62, value64, value66, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (324 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 183 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 99 = true := by
  rw [value62, value64, value66, value99, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(324 : Vertex), (328 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(324 : Vertex), (328 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 183 = true ∨ valuation q 63 = true ∨ valuation q 66 = true ∨ valuation q 99 = true := by
  rw [value62, value63, value66, value99, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(321 : Vertex), (328 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (324 : Vertex) [(321 : Vertex), (328 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E019.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112019
