import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 54 = true := by
  rw [value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (356 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 44 = true ∨ valuation q 55 = true := by
  rw [value44, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ∈ [(324 : Vertex), (358 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (356 : Vertex) [(324 : Vertex), (358 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 44 = false ∨ valuation q 55 = false := by
  rw [value44, value55, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (356 : Vertex) (324 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 176 = true ∨ valuation q 55 = true := by
  rw [value54, value55, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(358 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (324 : Vertex) [(358 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 176 = true ∨ valuation q 44 = true := by
  rw [value44, value54, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (358 : Vertex) → w ∈ [(324 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (358 : Vertex) [(324 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 177 = true ∨ valuation q 113 = true := by
  rw [value55, value113, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (356 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 177 = true ∨ valuation q 54 = true := by
  rw [value54, value55, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (486 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 178 = true ∨ valuation q 59 = true := by
  rw [value56, value59, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(376 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (488 : Vertex) [(376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 32 = false ∨ valuation q 48 = false ∨ valuation q 58 = false := by
  rw [value32, value48, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (336 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 32 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value32, value57, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (370 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 48 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value48, value57, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (336 : Vertex) (370 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 48 = false ∨ valuation q 58 = false := by
  rw [value48, value58, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (368 : Vertex) (336 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 49 = false ∨ valuation q 61 = false ∨ valuation q 118 = false := by
  rw [value49, value58, value61, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (370 : Vertex) (338 : Vertex) (378 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 180 = true ∨ valuation q 49 = true ∨ valuation q 57 = true ∨ valuation q 61 = true := by
  rw [value49, value57, value58, value61, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(338 : Vertex), (368 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (498 : Vertex) [(338 : Vertex), (368 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 37 = false ∨ valuation q 50 = false ∨ valuation q 61 = false := by
  rw [value37, value50, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (312 : Vertex) (344 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 37 = false ∨ valuation q 56 = false ∨ valuation q 61 = false := by
  rw [value37, value56, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (312 : Vertex) (360 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 37 = false ∨ valuation q 60 = false ∨ valuation q 120 = false := by
  rw [value37, value59, value60, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (312 : Vertex) (377 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 37 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value37, value59, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (312 : Vertex) (378 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value56, value57, value59, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (376 : Vertex) (360 : Vertex) (368 : Vertex) (380 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 38 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value38, value58, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (370 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 38 = false ∨ valuation q 58 = false ∨ valuation q 62 = false := by
  rw [value38, value58, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (370 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 38 = false ∨ valuation q 58 = false ∨ valuation q 121 = false := by
  rw [value38, value58, value61, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (370 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 38 = false ∨ valuation q 62 = false ∨ valuation q 121 = false := by
  rw [value38, value61, value62, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (379 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 184 = true ∨ valuation q 61 = true := by
  rw [value61, value62, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(378 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (377 : Vertex) [(378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 184 = true ∨ valuation q 60 = true := by
  rw [value60, value62, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(377 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (378 : Vertex) [(377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 185 = true ∨ valuation q 59 = true := by
  rw [value59, value63, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(376 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (508 : Vertex) [(376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value64, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 70 = false := by
  rw [value64, value65, value66, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 82 = false := by
  rw [value64, value65, value66, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 102 = false := by
  rw [value64, value65, value66, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value64, value65, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 82 = false := by
  rw [value64, value65, value67, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (388 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E254.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112254
