import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value4, value52, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 63 = false ∨ valuation q 90 = false := by
  rw [value4, value52, value63, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (280 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value4, value52, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value45, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 63 = false := by
  rw [value45, value52, value53, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (266 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 72 = false := by
  rw [value45, value52, value53, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (266 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 90 = false := by
  rw [value45, value52, value53, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (266 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value45, value52, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 55 = false ∨ valuation q 72 = false := by
  rw [value45, value52, value55, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value45, value52, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (268 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value45, value52, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 63 = false ∨ valuation q 90 = false := by
  rw [value45, value52, value63, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (280 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value45, value52, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value52, value53, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 72 = false := by
  rw [value52, value53, value55, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value52, value53, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value52, value53, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 90 = false := by
  rw [value52, value53, value63, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (280 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value52, value53, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value52, value55, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (268 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 63 = false ∨ valuation q 90 = false := by
  rw [value52, value55, value63, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (268 : Vertex) (280 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value52, value55, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (268 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 63 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value52, value63, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (280 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 45 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 63 = true ∨ valuation q 72 = true ∨ valuation q 90 = true := by
  rw [value45, value52, value53, value55, value63, value72, value90, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(256 : Vertex), (266 : Vertex), (268 : Vertex), (280 : Vertex), (328 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (8 : Vertex) [(256 : Vertex), (266 : Vertex), (268 : Vertex), (280 : Vertex), (328 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 4 = true ∨ valuation q 45 = true ∨ valuation q 55 = true ∨ valuation q 63 = true ∨ valuation q 72 = true ∨ valuation q 90 = true := by
  rw [value4, value45, value52, value55, value63, value72, value90, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(8 : Vertex), (256 : Vertex), (268 : Vertex), (280 : Vertex), (328 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (266 : Vertex) [(8 : Vertex), (256 : Vertex), (268 : Vertex), (280 : Vertex), (328 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 4 = true ∨ valuation q 45 = true ∨ valuation q 53 = true ∨ valuation q 63 = true ∨ valuation q 72 = true ∨ valuation q 90 = true := by
  rw [value4, value45, value52, value53, value63, value72, value90, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(8 : Vertex), (256 : Vertex), (266 : Vertex), (280 : Vertex), (328 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (268 : Vertex) [(8 : Vertex), (256 : Vertex), (266 : Vertex), (280 : Vertex), (328 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 4 = true ∨ valuation q 45 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 72 = true ∨ valuation q 90 = true := by
  rw [value4, value45, value52, value53, value55, value72, value90, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(8 : Vertex), (256 : Vertex), (266 : Vertex), (268 : Vertex), (328 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (280 : Vertex) [(8 : Vertex), (256 : Vertex), (266 : Vertex), (268 : Vertex), (328 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 4 = true ∨ valuation q 45 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 63 = true ∨ valuation q 90 = true := by
  rw [value4, value45, value52, value53, value55, value63, value90, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(8 : Vertex), (256 : Vertex), (266 : Vertex), (268 : Vertex), (280 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (328 : Vertex) [(8 : Vertex), (256 : Vertex), (266 : Vertex), (268 : Vertex), (280 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 4 = true ∨ valuation q 45 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 63 = true ∨ valuation q 72 = true := by
  rw [value4, value45, value52, value53, value55, value63, value72, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(8 : Vertex), (256 : Vertex), (266 : Vertex), (268 : Vertex), (280 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (392 : Vertex) [(8 : Vertex), (256 : Vertex), (266 : Vertex), (268 : Vertex), (280 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (264 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 65 = false := by
  rw [value52, value53, value54, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (264 : Vertex) (267 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value53, value54, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (267 : Vertex) (270 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E207.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112207
