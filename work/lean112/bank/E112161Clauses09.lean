import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 52 = true ∨ valuation q 66 = true ∨ valuation q 75 = true := by
  rw [value52, value66, value67, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ∈ [(267 : Vertex), (330 : Vertex), (347 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (331 : Vertex) [(267 : Vertex), (330 : Vertex), (347 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 178 = true ∨ valuation q 66 = true ∨ valuation q 75 = true := by
  rw [value66, value67, value75, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(330 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (267 : Vertex) [(330 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 178 = true ∨ valuation q 52 = true ∨ valuation q 75 = true := by
  rw [value52, value67, value75, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(267 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (330 : Vertex) [(267 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 178 = true ∨ valuation q 52 = true ∨ valuation q 66 = true := by
  rw [value52, value66, value67, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(267 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (347 : Vertex) [(267 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value63, value68, value69, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (324 : Vertex) (333 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 179 = true ∨ valuation q 63 = true ∨ valuation q 76 = true := by
  rw [value63, value68, value76, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(324 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (333 : Vertex) [(324 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 179 = true ∨ valuation q 63 = true ∨ valuation q 69 = true := by
  rw [value63, value68, value69, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(324 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (348 : Vertex) [(324 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 180 = true ∨ valuation q 68 = true := by
  rw [value68, value69, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(332 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (325 : Vertex) [(332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 180 = true ∨ valuation q 64 = true := by
  rw [value64, value69, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(325 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (332 : Vertex) [(325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 61 = true ∨ valuation q 71 = true := by
  rw [value61, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ∈ [(320 : Vertex), (337 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (336 : Vertex) [(320 : Vertex), (337 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 181 = true ∨ valuation q 71 = true := by
  rw [value70, value71, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(337 : Vertex)] := by decide
  have hg := other_cover q (336 : Vertex) (320 : Vertex) [(337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 181 = true ∨ valuation q 61 = true := by
  rw [value61, value70, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (336 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(320 : Vertex)] := by decide
  have hg := other_cover q (336 : Vertex) (337 : Vertex) [(320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value70, value71, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (336 : Vertex) (339 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 182 = true ∨ valuation q 72 = true ∨ valuation q 74 = true := by
  rw [value71, value72, value74, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(339 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (336 : Vertex) [(339 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 182 = true ∨ valuation q 70 = true ∨ valuation q 74 = true := by
  rw [value70, value71, value74, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(336 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(336 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 182 = true ∨ valuation q 70 = true ∨ valuation q 72 = true := by
  rw [value70, value71, value72, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(336 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (345 : Vertex) [(336 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 183 = true ∨ valuation q 71 = true ∨ valuation q 75 = true := by
  rw [value71, value72, value75, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(337 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (343 : Vertex) [(337 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 183 = true ∨ valuation q 71 = true ∨ valuation q 73 = true := by
  rw [value71, value72, value73, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(337 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (347 : Vertex) [(337 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 57 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value57, value72, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (279 : Vertex) (339 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 78 = true := by
  rw [value57, value73, value78, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(279 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (339 : Vertex) [(279 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 72 = true := by
  rw [value57, value72, value73, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(279 : Vertex), (339 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (351 : Vertex) [(279 : Vertex), (339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 59 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value59, value71, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (281 : Vertex) (337 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 185 = true ∨ valuation q 71 = true ∨ valuation q 75 = true := by
  rw [value71, value74, value75, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(337 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (281 : Vertex) [(337 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 185 = true ∨ valuation q 59 = true ∨ valuation q 75 = true := by
  rw [value59, value74, value75, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(281 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (337 : Vertex) [(281 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value67, value72, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (339 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value67, value72, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (339 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 67 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value67, value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (331 : Vertex) (345 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 72 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value72, value74, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (347 : Vertex) (339 : Vertex) (345 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 76 = true := by
  rw [value76, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (348 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 187 = true ∨ valuation q 77 = true := by
  rw [value76, value77, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (332 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 187 = true ∨ valuation q 68 = true := by
  rw [value68, value76, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(332 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 188 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(351 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E161.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112161
