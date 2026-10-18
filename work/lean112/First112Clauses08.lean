import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 65 = true ∨ valuation q 66 = true := by
  rw [value65, value66, value67, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(305 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (435 : Vertex) [(305 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 58 = false ∨ valuation q 66 = false ∨ valuation q 71 = false := by
  rw [value58, value66, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (306 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 190 = true ∨ valuation q 66 = true ∨ valuation q 71 = true := by
  rw [value66, value68, value71, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(306 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (294 : Vertex) [(306 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 190 = true ∨ valuation q 58 = true ∨ valuation q 71 = true := by
  rw [value58, value68, value71, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(294 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (306 : Vertex) [(294 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 190 = true ∨ valuation q 58 = true ∨ valuation q 66 = true := by
  rw [value58, value66, value68, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(294 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (318 : Vertex) [(294 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 191 = true ∨ valuation q 71 = true := by
  rw [value69, value71, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (317 : Vertex) [(318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 191 = true ∨ valuation q 70 = true := by
  rw [value69, value70, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(317 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (318 : Vertex) [(317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 62 = false ∨ valuation q 69 = false := by
  rw [value62, value69, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (317 : Vertex) (301 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 192 = true ∨ valuation q 69 = true := by
  rw [value69, value70, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(316 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (301 : Vertex) [(316 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 192 = true ∨ valuation q 62 = true := by
  rw [value62, value70, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(301 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (316 : Vertex) [(301 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value68, value69, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (318 : Vertex) (310 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 193 = true ∨ valuation q 69 = true := by
  rw [value69, value71, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(316 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (310 : Vertex) [(316 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 193 = true ∨ valuation q 68 = true := by
  rw [value68, value71, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(310 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (316 : Vertex) [(310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 55 = false ∨ valuation q 74 = false ∨ valuation q 103 = false := by
  rw [value55, value72, value74, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (288 : Vertex) (356 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 194 = true ∨ valuation q 55 = true ∨ valuation q 103 = true := by
  rw [value55, value72, value103, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (352 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(288 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (352 : Vertex) (356 : Vertex) [(288 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 17 = false ∨ valuation q 75 = false ∨ valuation q 106 = false := by
  rw [value17, value73, value75, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (99 : Vertex) (359 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 195 = true ∨ valuation q 75 = true ∨ valuation q 106 = true := by
  rw [value73, value75, value106, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(359 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (99 : Vertex) [(359 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 195 = true ∨ valuation q 17 = true ∨ valuation q 106 = true := by
  rw [value17, value73, value106, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(99 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (359 : Vertex) [(99 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 195 = true ∨ valuation q 17 = true ∨ valuation q 75 = true := by
  rw [value17, value73, value75, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(99 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (483 : Vertex) [(99 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 18 = false ∨ valuation q 72 = false ∨ valuation q 76 = false := by
  rw [value18, value72, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (100 : Vertex) (352 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 18 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value18, value74, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (100 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 72 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value72, value74, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (352 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value76, value77, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (356 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 196 = true ∨ valuation q 18 = true ∨ valuation q 72 = true ∨ valuation q 77 = true := by
  rw [value18, value72, value74, value77, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (364 : Vertex) → w ∈ [(100 : Vertex), (352 : Vertex), (372 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (364 : Vertex) [(100 : Vertex), (352 : Vertex), (372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 19 = false ∨ valuation q 59 = false ∨ valuation q 79 = false := by
  rw [value19, value59, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (295 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 19 = false ∨ valuation q 73 = false ∨ valuation q 79 = false := by
  rw [value19, value73, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (355 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 59 = false ∨ valuation q 73 = false ∨ valuation q 79 = false := by
  rw [value59, value73, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (355 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 19 = false ∨ valuation q 79 = false := by
  rw [value19, value79, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (359 : Vertex) (103 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 197 = true ∨ valuation q 59 = true ∨ valuation q 73 = true ∨ valuation q 79 = true := by
  rw [value59, value73, value75, value79, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(295 : Vertex), (355 : Vertex), (375 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (103 : Vertex) [(295 : Vertex), (355 : Vertex), (375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 197 = true ∨ valuation q 19 = true ∨ valuation q 59 = true ∨ valuation q 79 = true := by
  rw [value19, value59, value75, value79, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(103 : Vertex), (295 : Vertex), (375 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (355 : Vertex) [(103 : Vertex), (295 : Vertex), (375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 197 = true ∨ valuation q 19 = true ∨ valuation q 59 = true ∨ valuation q 73 = true := by
  rw [value19, value59, value73, value75, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(103 : Vertex), (295 : Vertex), (355 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (375 : Vertex) [(103 : Vertex), (295 : Vertex), (355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = true := by
  rw [value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ∈ [(356 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (364 : Vertex) [(356 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.First112
