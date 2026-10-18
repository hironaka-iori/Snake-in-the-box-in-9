import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 177 = true ∨ valuation q 51 = true ∨ valuation q 57 = true := by
  rw [value51, value56, value57, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(293 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (317 : Vertex) [(293 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value53, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 93 = false := by
  rw [value53, value55, value57, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 93 = false := by
  rw [value53, value56, value57, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 93 = false := by
  rw [value55, value56, value57, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (299 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 178 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 93 = true := by
  rw [value53, value55, value57, value93, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(295 : Vertex), (299 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (301 : Vertex) [(295 : Vertex), (299 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 179 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value58, value59, value60, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(305 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (288 : Vertex) [(305 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 179 = true ∨ valuation q 49 = true ∨ valuation q 60 = true := by
  rw [value49, value58, value60, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (304 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(288 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (304 : Vertex) (305 : Vertex) [(288 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 50 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value50, value58, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (304 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 50 = false ∨ valuation q 61 = false ∨ valuation q 94 = false := by
  rw [value50, value59, value61, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 94 = false := by
  rw [value58, value59, value61, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (304 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 180 = true ∨ valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 94 = true := by
  rw [value58, value59, value61, value94, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(304 : Vertex), (307 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (289 : Vertex) [(304 : Vertex), (307 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value58, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (304 : Vertex) (307 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 182 = true ∨ valuation q 60 = true ∨ valuation q 95 = true := by
  rw [value60, value61, value95, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(306 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(306 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 182 = true ∨ valuation q 59 = true ∨ valuation q 95 = true := by
  rw [value59, value61, value95, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(305 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (306 : Vertex) [(305 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 182 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value59, value60, value61, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(305 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (435 : Vertex) [(305 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 52 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value52, value60, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (310 : Vertex) (294 : Vertex) (306 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 183 = true ∨ valuation q 52 = true ∨ valuation q 65 = true := by
  rw [value52, value62, value65, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(294 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (306 : Vertex) [(294 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 183 = true ∨ valuation q 52 = true ∨ valuation q 60 = true := by
  rw [value52, value60, value62, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(294 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (318 : Vertex) [(294 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 184 = true ∨ valuation q 65 = true := by
  rw [value63, value65, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (317 : Vertex) [(318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 184 = true ∨ valuation q 64 = true := by
  rw [value63, value64, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(317 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (318 : Vertex) [(317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 185 = true ∨ valuation q 56 = true := by
  rw [value56, value64, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(301 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (316 : Vertex) [(301 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 186 = true ∨ valuation q 63 = true := by
  rw [value63, value65, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(316 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (310 : Vertex) [(316 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 187 = true ∨ valuation q 67 = true := by
  rw [value66, value67, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (354 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(355 : Vertex)] := by decide
  have hg := other_cover q (354 : Vertex) (362 : Vertex) [(355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 188 = true ∨ valuation q 9 = true ∨ valuation q 71 = true := by
  rw [value9, value67, value71, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(99 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (354 : Vertex) [(99 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 188 = true ∨ valuation q 9 = true ∨ valuation q 66 = true := by
  rw [value9, value66, value67, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(99 : Vertex), (354 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (363 : Vertex) [(99 : Vertex), (354 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 10 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value10, value68, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (100 : Vertex) (357 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 10 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value10, value68, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (100 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value68, value69, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (357 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 189 = true ∨ valuation q 10 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value10, value68, value69, value72, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(100 : Vertex), (357 : Vertex), (364 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (372 : Vertex) [(100 : Vertex), (357 : Vertex), (364 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 51 = false ∨ valuation q 68 = false ∨ valuation q 75 = false := by
  rw [value51, value68, value69, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (293 : Vertex) (356 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 190 = true ∨ valuation q 51 = true ∨ valuation q 75 = true := by
  rw [value51, value69, value75, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(293 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (356 : Vertex) [(293 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E024.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112024
