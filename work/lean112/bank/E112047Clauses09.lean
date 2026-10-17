import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 64 = true := by
  rw [value64, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (322 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 50 = false ∨ valuation q 62 = false ∨ valuation q 69 = false := by
  rw [value50, value62, value64, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (320 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 50 = false ∨ valuation q 62 = false ∨ valuation q 72 = false := by
  rw [value50, value62, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (320 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 50 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value50, value64, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (326 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 50 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value50, value64, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (326 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 50 = false ∨ valuation q 65 = false ∨ valuation q 100 = false := by
  rw [value50, value64, value65, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (326 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 50 = false ∨ valuation q 72 = false ∨ valuation q 100 = false := by
  rw [value50, value64, value72, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (338 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 69 = false := by
  rw [value62, value64, value65, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value62, value64, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 62 = false ∨ valuation q 72 = false ∨ valuation q 100 = false := by
  rw [value62, value64, value72, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (338 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value64, value65, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (326 : Vertex) (330 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 100 = false := by
  rw [value64, value65, value69, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (326 : Vertex) (330 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 72 = false ∨ valuation q 100 = false := by
  rw [value64, value65, value72, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (326 : Vertex) (338 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 71 = false := by
  rw [value64, value65, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (327 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 183 = true ∨ valuation q 64 = true ∨ valuation q 71 = true := by
  rw [value64, value65, value71, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(322 : Vertex), (334 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(322 : Vertex), (334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 183 = true ∨ valuation q 64 = true ∨ valuation q 66 = true := by
  rw [value64, value65, value66, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(322 : Vertex), (327 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (334 : Vertex) [(322 : Vertex), (327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 65 = true ∨ valuation q 74 = true := by
  rw [value65, value66, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ∈ [(326 : Vertex), (343 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (327 : Vertex) [(326 : Vertex), (343 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 65 = false ∨ valuation q 74 = false := by
  rw [value65, value74, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (327 : Vertex) (326 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 74 = true := by
  rw [value66, value74, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 65 = true := by
  rw [value65, value66, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (343 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 10 = true ∨ valuation q 62 = true ∨ valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 70 = true := by
  rw [value10, value62, value67, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (320 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (328 : Vertex) [(72 : Vertex), (320 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 10 = false ∨ valuation q 62 = false ∨ valuation q 69 = false := by
  rw [value10, value62, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (72 : Vertex) (320 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 10 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value10, value62, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (72 : Vertex) (320 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 62 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value62, value67, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (320 : Vertex) (329 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 62 = true ∨ valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 70 = true := by
  rw [value62, value67, value68, value69, value70, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (72 : Vertex) [(320 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 10 = true ∨ valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 70 = true := by
  rw [value10, value67, value68, value69, value70, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(72 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(72 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 10 = true ∨ valuation q 62 = true ∨ valuation q 69 = true ∨ valuation q 70 = true := by
  rw [value10, value62, value67, value69, value70, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(72 : Vertex), (320 : Vertex), (330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (329 : Vertex) [(72 : Vertex), (320 : Vertex), (330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 10 = true ∨ valuation q 62 = true ∨ valuation q 68 = true ∨ valuation q 69 = true := by
  rw [value10, value62, value67, value68, value69, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(72 : Vertex), (320 : Vertex), (329 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (332 : Vertex) [(72 : Vertex), (320 : Vertex), (329 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 75 = false := by
  rw [value63, value67, value68, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 75 = false ∨ valuation q 104 = false := by
  rw [value63, value68, value75, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (345 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 52 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value52, value64, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (322 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 52 = false ∨ valuation q 64 = false ∨ valuation q 71 = false := by
  rw [value52, value64, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (322 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E047.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112047
