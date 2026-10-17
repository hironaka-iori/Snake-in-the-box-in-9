import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value46, value54, value56, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (282 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value54, value55, value56, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (281 : Vertex) (282 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 162 = true ∨ valuation q 54 = true ∨ valuation q 57 = true := by
  rw [value54, value55, value57, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(280 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (265 : Vertex) [(280 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 162 = true ∨ valuation q 47 = true ∨ valuation q 57 = true := by
  rw [value47, value55, value57, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(265 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (280 : Vertex) [(265 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 162 = true ∨ valuation q 47 = true ∨ valuation q 54 = true := by
  rw [value47, value54, value55, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(265 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (283 : Vertex) [(265 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 4 = false ∨ valuation q 48 = false ∨ valuation q 57 = false := by
  rw [value4, value48, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (26 : Vertex) (266 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 4 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value4, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (26 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value51, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (274 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 71 = false := by
  rw [value51, value54, value56, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (274 : Vertex) (280 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 57 = false ∨ valuation q 71 = false := by
  rw [value51, value56, value57, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (274 : Vertex) (283 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 72 = false := by
  rw [value49, value55, value57, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (281 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 72 = false := by
  rw [value49, value56, value57, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (282 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 72 = false := by
  rw [value55, value56, value57, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (281 : Vertex) (282 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 165 = true ∨ valuation q 54 = true ∨ valuation q 73 = true := by
  rw [value54, value58, value73, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(280 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (276 : Vertex) [(280 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 165 = true ∨ valuation q 52 = true ∨ valuation q 73 = true := by
  rw [value52, value58, value73, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(276 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (280 : Vertex) [(276 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 166 = true ∨ valuation q 61 = true := by
  rw [value59, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(322 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 166 = true ∨ valuation q 60 = true := by
  rw [value59, value60, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(321 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (322 : Vertex) [(321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 167 = true ∨ valuation q 41 = true ∨ valuation q 63 = true := by
  rw [value41, value60, value63, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(257 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(257 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 67 = false := by
  rw [value59, value61, value62, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 44 = false ∨ valuation q 61 = false ∨ valuation q 66 = false := by
  rw [value44, value61, value62, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (322 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 171 = true ∨ valuation q 66 = true ∨ valuation q 73 = true := by
  rw [value64, value66, value73, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(334 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (333 : Vertex) [(334 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 171 = true ∨ valuation q 65 = true ∨ valuation q 73 = true := by
  rw [value64, value65, value73, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(333 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (334 : Vertex) [(333 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value63, value64, value65, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (332 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value67, value68, value70, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (339 : Vertex) (338 : Vertex) (343 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 176 = true ∨ valuation q 70 = true := by
  rw [value69, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (349 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 177 = true ∨ valuation q 68 = true := by
  rw [value68, value70, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (341 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 56 = false ∨ valuation q 72 = false ∨ valuation q 97 = false := by
  rw [value56, value71, value72, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (347 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 178 = true ∨ valuation q 56 = true ∨ valuation q 67 = true ∨ valuation q 72 = true := by
  rw [value56, value67, value71, value72, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(282 : Vertex), (338 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (474 : Vertex) [(282 : Vertex), (338 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 57 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value57, value68, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (283 : Vertex) (339 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 179 = true ∨ valuation q 57 = true ∨ valuation q 71 = true := by
  rw [value57, value71, value72, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (347 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(283 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (347 : Vertex) (339 : Vertex) [(283 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value58, value64, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (284 : Vertex) (332 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 181 = true ∨ valuation q 69 = true ∨ valuation q 73 = true := by
  rw [value69, value73, value74, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(341 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (333 : Vertex) [(341 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E151.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112151
