import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true ∨ valuation q 53 = true ∨ valuation q 90 = true := by
  rw [value53, value54, value90, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(272 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (275 : Vertex) [(272 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 91 = false := by
  rw [value51, value54, value55, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (259 : Vertex) (273 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 54 = true ∨ valuation q 91 = true := by
  rw [value54, value55, value91, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(273 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (259 : Vertex) [(273 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 51 = true ∨ valuation q 91 = true := by
  rw [value51, value55, value91, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(259 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (273 : Vertex) [(259 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 51 = true ∨ valuation q 54 = true := by
  rw [value51, value54, value55, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(259 : Vertex), (273 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (403 : Vertex) [(259 : Vertex), (273 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 56 = true := by
  rw [value56, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (276 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 57 = true ∨ valuation q 59 = true := by
  rw [value56, value57, value59, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 53 = true ∨ valuation q 59 = true := by
  rw [value53, value56, value59, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(272 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (278 : Vertex) [(272 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 53 = true ∨ valuation q 57 = true := by
  rw [value53, value56, value57, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(272 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (284 : Vertex) [(272 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value7, value56, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (276 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 60 = false ∨ valuation q 93 = false := by
  rw [value7, value57, value60, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (286 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 93 = false := by
  rw [value56, value57, value60, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (276 : Vertex) (286 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 58 = true := by
  rw [value58, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (280 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 53 = true ∨ valuation q 59 = true ∨ valuation q 95 = true := by
  rw [value53, value58, value59, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ∈ [(272 : Vertex), (284 : Vertex), (408 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (280 : Vertex) [(272 : Vertex), (284 : Vertex), (408 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 59 = true ∨ valuation q 95 = true := by
  rw [value58, value59, value95, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(284 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (272 : Vertex) [(284 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 53 = true ∨ valuation q 95 = true := by
  rw [value53, value58, value95, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(272 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (284 : Vertex) [(272 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 53 = true ∨ valuation q 59 = true := by
  rw [value53, value58, value59, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(272 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (408 : Vertex) [(272 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 60 = false := by
  rw [value56, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (276 : Vertex) (280 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 177 = true ∨ valuation q 56 = true ∨ valuation q 58 = true := by
  rw [value56, value58, value59, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(276 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (286 : Vertex) [(276 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value57, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (286 : Vertex) (278 : Vertex) (284 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value57, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (286 : Vertex) (278 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value59, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (286 : Vertex) (284 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 178 = true ∨ valuation q 57 = true ∨ valuation q 59 = true := by
  rw [value57, value59, value60, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (287 : Vertex) [(278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 60 = true := by
  rw [value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ∈ [(286 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (287 : Vertex) [(286 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 61 = true := by
  rw [value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value62, value63, value64, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 180 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value62, value64, value67, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(322 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(322 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 180 = true ∨ valuation q 63 = true ∨ valuation q 64 = true := by
  rw [value62, value63, value64, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(321 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(321 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 8 = true ∨ valuation q 62 = true ∨ valuation q 68 = true := by
  rw [value8, value62, value63, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ∈ [(65 : Vertex), (320 : Vertex), (329 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (321 : Vertex) [(65 : Vertex), (320 : Vertex), (329 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 62 = true ∨ valuation q 68 = true := by
  rw [value62, value63, value68, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (65 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 8 = true ∨ valuation q 68 = true := by
  rw [value8, value63, value68, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(65 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(65 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 8 = true ∨ valuation q 62 = true := by
  rw [value8, value62, value63, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(65 : Vertex), (320 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (329 : Vertex) [(65 : Vertex), (320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E047.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112047
