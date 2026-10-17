import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 74 = false := by
  rw [value55, value56, value60, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (273 : Vertex) (280 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value56, value60, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (272 : Vertex) (273 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 172 = true ∨ valuation q 60 = true ∨ valuation q 74 = true := by
  rw [value55, value60, value74, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(280 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (273 : Vertex) [(280 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 172 = true ∨ valuation q 56 = true ∨ valuation q 74 = true := by
  rw [value55, value56, value74, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(273 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (280 : Vertex) [(273 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value55, value56, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (272 : Vertex) (277 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 61 = true := by
  rw [value55, value56, value57, value61, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(272 : Vertex), (275 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (277 : Vertex) [(272 : Vertex), (275 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 174 = true ∨ valuation q 59 = true ∨ valuation q 76 = true := by
  rw [value57, value59, value76, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(279 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (273 : Vertex) [(279 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value49, value56, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (273 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 49 = false ∨ valuation q 56 = false := by
  rw [value49, value56, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (277 : Vertex) (261 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 175 = true ∨ valuation q 56 = true ∨ valuation q 59 = true := by
  rw [value56, value58, value59, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(273 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (261 : Vertex) [(273 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 58 = false ∨ valuation q 63 = false ∨ valuation q 79 = false := by
  rw [value58, value59, value63, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (277 : Vertex) (287 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 176 = true ∨ valuation q 58 = true ∨ valuation q 63 = true ∨ valuation q 79 = true := by
  rw [value58, value59, value63, value79, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(277 : Vertex), (287 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (275 : Vertex) [(277 : Vertex), (287 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 176 = true ∨ valuation q 57 = true ∨ valuation q 63 = true ∨ valuation q 79 = true := by
  rw [value57, value59, value63, value79, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(275 : Vertex), (287 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (277 : Vertex) [(275 : Vertex), (287 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 177 = true ∨ valuation q 61 = true ∨ valuation q 80 = true := by
  rw [value60, value61, value80, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(281 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (272 : Vertex) [(281 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 177 = true ∨ valuation q 55 = true ∨ valuation q 80 = true := by
  rw [value55, value60, value80, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(272 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (281 : Vertex) [(272 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 177 = true ∨ valuation q 55 = true ∨ valuation q 61 = true := by
  rw [value55, value60, value61, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(272 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (344 : Vertex) [(272 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value51, value56, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (273 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 81 = false := by
  rw [value51, value56, value61, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (273 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 81 = false := by
  rw [value51, value60, value61, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 81 = false := by
  rw [value56, value60, value61, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (273 : Vertex) (280 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value56, value60, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (281 : Vertex) (273 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 56 = true ∨ valuation q 60 = true ∨ valuation q 81 = true := by
  rw [value56, value60, value61, value81, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(273 : Vertex), (280 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (265 : Vertex) [(273 : Vertex), (280 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 51 = true ∨ valuation q 60 = true ∨ valuation q 81 = true := by
  rw [value51, value60, value61, value81, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(265 : Vertex), (280 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (273 : Vertex) [(265 : Vertex), (280 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 51 = true ∨ valuation q 56 = true ∨ valuation q 81 = true := by
  rw [value51, value56, value61, value81, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(265 : Vertex), (273 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (280 : Vertex) [(265 : Vertex), (273 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 63 = true ∨ valuation q 85 = true := by
  rw [value62, value63, value85, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(287 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (270 : Vertex) [(287 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 54 = true ∨ valuation q 85 = true := by
  rw [value54, value62, value85, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(270 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (287 : Vertex) [(270 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 54 = true ∨ valuation q 63 = true := by
  rw [value54, value62, value63, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(270 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (350 : Vertex) [(270 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 86 = false := by
  rw [value59, value62, value63, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (286 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 59 = false ∨ valuation q 62 = false := by
  rw [value59, value62, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (287 : Vertex) (279 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 62 = false ∨ valuation q 86 = false := by
  rw [value62, value86, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (287 : Vertex) (286 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 62 = true ∨ valuation q 86 = true := by
  rw [value62, value63, value86, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(286 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(286 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 59 = true ∨ valuation q 86 = true := by
  rw [value59, value63, value86, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(279 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (286 : Vertex) [(279 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E064.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112064
