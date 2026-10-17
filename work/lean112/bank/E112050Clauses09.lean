import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 68 = true ∨ valuation q 83 = true := by
  rw [value68, value74, value83, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(322 : Vertex), (346 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (328 : Vertex) [(322 : Vertex), (346 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 202 = true ∨ valuation q 68 = true ∨ valuation q 73 = true := by
  rw [value68, value73, value74, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(322 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (346 : Vertex) [(322 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 3 = false ∨ valuation q 56 = false ∨ valuation q 69 = false := by
  rw [value3, value56, value69, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (76 : Vertex) (268 : Vertex) (324 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 3 = false ∨ valuation q 56 = false ∨ valuation q 73 = false := by
  rw [value3, value56, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (76 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 3 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value3, value69, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (76 : Vertex) (324 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 56 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value56, value69, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (324 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value78, value82, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (337 : Vertex) (341 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 82 = true := by
  rw [value76, value82, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (341 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 204 = true ∨ valuation q 78 = true := by
  rw [value76, value78, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (345 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 69 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value69, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (324 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 205 = true ∨ valuation q 69 = true ∨ valuation q 78 = true := by
  rw [value69, value77, value78, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(324 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (342 : Vertex) [(324 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 70 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value70, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (325 : Vertex) (337 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 206 = true ∨ valuation q 70 = true ∨ valuation q 77 = true ∨ valuation q 80 = true := by
  rw [value70, value77, value78, value80, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(325 : Vertex), (340 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (337 : Vertex) [(325 : Vertex), (340 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 206 = true ∨ valuation q 70 = true ∨ valuation q 76 = true ∨ valuation q 80 = true := by
  rw [value70, value76, value78, value80, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(325 : Vertex), (337 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (340 : Vertex) [(325 : Vertex), (337 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 77 = true ∨ valuation q 80 = true := by
  rw [value77, value79, value80, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(340 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (326 : Vertex) [(340 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 71 = true ∨ valuation q 80 = true := by
  rw [value71, value79, value80, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(326 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (340 : Vertex) [(326 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 207 = true ∨ valuation q 71 = true ∨ valuation q 77 = true := by
  rw [value71, value77, value79, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(326 : Vertex), (340 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (343 : Vertex) [(326 : Vertex), (340 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 72 = false := by
  rw [value7, value62, value72, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 78 = false := by
  rw [value7, value62, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 79 = false := by
  rw [value7, value62, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 85 = false := by
  rw [value7, value62, value80, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 62 = false ∨ valuation q 123 = false := by
  rw [value7, value62, value80, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (279 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value7, value72, value78, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 72 = false ∨ valuation q 79 = false := by
  rw [value7, value72, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 72 = false ∨ valuation q 85 = false := by
  rw [value7, value72, value80, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 72 = false ∨ valuation q 123 = false := by
  rw [value7, value72, value80, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (327 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value7, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (341 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 78 = false ∨ valuation q 85 = false := by
  rw [value7, value78, value80, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (341 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 78 = false ∨ valuation q 123 = false := by
  rw [value7, value78, value80, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (341 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value7, value79, value80, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (342 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 79 = false ∨ valuation q 123 = false := by
  rw [value7, value79, value80, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (342 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 85 = false ∨ valuation q 123 = false := by
  rw [value7, value80, value85, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (343 : Vertex) (87 : Vertex) (351 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E050.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112050
