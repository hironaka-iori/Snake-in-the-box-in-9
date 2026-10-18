import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 102 = false := by
  rw [value64, value65, value67, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (388 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 82 = false := by
  rw [value64, value65, value70, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (392 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 70 = false ∨ valuation q 102 = false := by
  rw [value64, value65, value70, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value64, value65, value82, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (416 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value64, value66, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 82 = false := by
  rw [value64, value66, value67, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 102 = false := by
  rw [value64, value66, value67, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 70 = false ∨ valuation q 82 = false := by
  rw [value64, value66, value70, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 70 = false ∨ valuation q 102 = false := by
  rw [value64, value66, value70, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value64, value66, value82, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (416 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 82 = false := by
  rw [value64, value67, value70, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (388 : Vertex) (392 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 102 = false := by
  rw [value64, value67, value70, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (388 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value64, value67, value82, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (388 : Vertex) (416 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 70 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value64, value70, value82, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (392 : Vertex) (416 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 186 = true ∨ valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 82 = true := by
  rw [value64, value65, value66, value67, value70, value82, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(385 : Vertex), (386 : Vertex), (388 : Vertex), (392 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (448 : Vertex) [(385 : Vertex), (386 : Vertex), (388 : Vertex), (392 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 6 = false ∨ valuation q 64 = false ∨ valuation q 71 = false := by
  rw [value6, value64, value65, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (385 : Vertex) (257 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 187 = true ∨ valuation q 64 = true ∨ valuation q 71 = true := by
  rw [value64, value65, value71, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (257 : Vertex) [(384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 187 = true ∨ valuation q 6 = true ∨ valuation q 71 = true := by
  rw [value6, value65, value71, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(257 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (384 : Vertex) [(257 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 187 = true ∨ valuation q 6 = true ∨ valuation q 64 = true := by
  rw [value6, value64, value65, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(257 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (393 : Vertex) [(257 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 7 = false ∨ valuation q 64 = false ∨ valuation q 68 = false := by
  rw [value7, value64, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 7 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value7, value64, value66, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 7 = false ∨ valuation q 68 = false ∨ valuation q 74 = false := by
  rw [value7, value66, value68, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (390 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 188 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 74 = true := by
  rw [value64, value66, value68, value74, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (258 : Vertex) [(384 : Vertex), (390 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 188 = true ∨ valuation q 7 = true ∨ valuation q 68 = true ∨ valuation q 74 = true := by
  rw [value7, value66, value68, value74, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(258 : Vertex), (390 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(258 : Vertex), (390 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 188 = true ∨ valuation q 7 = true ∨ valuation q 64 = true ∨ valuation q 68 = true := by
  rw [value7, value64, value66, value68, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (402 : Vertex) [(258 : Vertex), (384 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value64, value67, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (390 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 75 = false := by
  rw [value64, value67, value68, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (390 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 75 = true ∨ valuation q 84 = true := by
  rw [value64, value67, value68, value75, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (404 : Vertex), (420 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (396 : Vertex) [(384 : Vertex), (390 : Vertex), (404 : Vertex), (420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 72 = true ∨ valuation q 84 = true := by
  rw [value64, value67, value68, value72, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (396 : Vertex), (420 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (404 : Vertex) [(384 : Vertex), (390 : Vertex), (396 : Vertex), (420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 68 = true ∨ valuation q 72 = true ∨ valuation q 75 = true := by
  rw [value64, value67, value68, value72, value75, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex), (396 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (420 : Vertex) [(384 : Vertex), (390 : Vertex), (396 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 9 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value9, value66, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (386 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 9 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value9, value66, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E254.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112254
