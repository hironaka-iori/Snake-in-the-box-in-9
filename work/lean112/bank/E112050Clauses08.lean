import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 85 = false := by
  rw [value65, value66, value67, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (285 : Vertex) (286 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 108 = false := by
  rw [value65, value66, value67, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (285 : Vertex) (286 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 85 = false ∨ valuation q 108 = false := by
  rw [value65, value67, value85, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (285 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 66 = false ∨ valuation q 85 = false ∨ valuation q 108 = false := by
  rw [value66, value67, value85, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (286 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 195 = true ∨ valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 85 = true ∨ valuation q 108 = true := by
  rw [value65, value66, value67, value85, value108, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(285 : Vertex), (286 : Vertex), (351 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(285 : Vertex), (286 : Vertex), (351 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 196 = true ∨ valuation q 2 = true ∨ valuation q 50 = true ∨ valuation q 71 = true := by
  rw [value2, value50, value68, value71, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(66 : Vertex), (258 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (330 : Vertex) [(66 : Vertex), (258 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value69, value70, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (325 : Vertex) (326 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value69, value71, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (326 : Vertex) (332 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value53, value69, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (324 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 113 = false := by
  rw [value53, value69, value70, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (324 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 53 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value53, value70, value72, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (327 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 53 = false ∨ valuation q 72 = false ∨ valuation q 113 = false := by
  rw [value53, value70, value72, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (327 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 53 = false ∨ valuation q 78 = false ∨ valuation q 113 = false := by
  rw [value53, value70, value78, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (341 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value69, value70, value72, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (324 : Vertex) (327 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 113 = false := by
  rw [value69, value70, value72, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (324 : Vertex) (327 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 78 = false ∨ valuation q 113 = false := by
  rw [value70, value72, value78, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (327 : Vertex) (341 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 198 = true ∨ valuation q 53 = true ∨ valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 78 = true := by
  rw [value53, value69, value70, value72, value78, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(261 : Vertex), (324 : Vertex), (327 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (453 : Vertex) [(261 : Vertex), (324 : Vertex), (327 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value68, value69, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (324 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 79 = false := by
  rw [value68, value69, value71, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (324 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 79 = false := by
  rw [value68, value71, value72, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 79 = false := by
  rw [value69, value71, value72, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (324 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 80 = false := by
  rw [value70, value71, value72, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (325 : Vertex) (326 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 114 = false := by
  rw [value70, value71, value72, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (325 : Vertex) (326 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 70 = false ∨ valuation q 80 = false ∨ valuation q 114 = false := by
  rw [value70, value72, value80, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (325 : Vertex) (343 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 71 = true ∨ valuation q 80 = true ∨ valuation q 114 = true := by
  rw [value71, value72, value80, value114, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(326 : Vertex), (343 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (325 : Vertex) [(326 : Vertex), (343 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 70 = true ∨ valuation q 80 = true ∨ valuation q 114 = true := by
  rw [value70, value72, value80, value114, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(325 : Vertex), (343 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(325 : Vertex), (343 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 114 = true := by
  rw [value70, value71, value72, value114, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(325 : Vertex), (326 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (343 : Vertex) [(325 : Vertex), (326 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 200 = true ∨ valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 80 = true := by
  rw [value70, value71, value72, value80, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(325 : Vertex), (326 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (455 : Vertex) [(325 : Vertex), (326 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 75 = true ∨ valuation q 81 = true := by
  rw [value73, value75, value81, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(332 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (330 : Vertex) [(332 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 74 = true ∨ valuation q 81 = true := by
  rw [value73, value74, value81, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(330 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (332 : Vertex) [(330 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 201 = true ∨ valuation q 74 = true ∨ valuation q 75 = true := by
  rw [value73, value74, value75, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (344 : Vertex) [(330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 68 = false ∨ valuation q 73 = false ∨ valuation q 83 = false := by
  rw [value68, value73, value74, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (328 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E050.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112050
