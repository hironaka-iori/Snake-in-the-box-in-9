import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 51 = true ∨ valuation q 61 = true ∨ valuation q 67 = true := by
  rw [value51, value61, value62, value67, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(263 : Vertex), (277 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (275 : Vertex) [(263 : Vertex), (277 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 51 = true ∨ valuation q 59 = true ∨ valuation q 67 = true := by
  rw [value51, value59, value62, value67, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(263 : Vertex), (275 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (277 : Vertex) [(263 : Vertex), (275 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 51 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value51, value59, value61, value62, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(263 : Vertex), (275 : Vertex), (277 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(263 : Vertex), (275 : Vertex), (277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 52 = true ∨ valuation q 64 = true ∨ valuation q 65 = true := by
  rw [value52, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ∈ [(264 : Vertex), (281 : Vertex), (282 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (280 : Vertex) [(264 : Vertex), (281 : Vertex), (282 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 64 = true ∨ valuation q 65 = true := by
  rw [value63, value64, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(281 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (264 : Vertex) [(281 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 52 = true ∨ valuation q 65 = true := by
  rw [value52, value63, value65, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(264 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (281 : Vertex) [(264 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 180 = true ∨ valuation q 52 = true ∨ valuation q 64 = true := by
  rw [value52, value63, value64, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(264 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (282 : Vertex) [(264 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 58 = false ∨ valuation q 63 = false ∨ valuation q 66 = false := by
  rw [value58, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (273 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 181 = true ∨ valuation q 58 = true ∨ valuation q 66 = true := by
  rw [value58, value64, value66, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(273 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (280 : Vertex) [(273 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 181 = true ∨ valuation q 58 = true ∨ valuation q 63 = true := by
  rw [value58, value63, value64, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(273 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (283 : Vertex) [(273 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 66 = false := by
  rw [value53, value63, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 81 = false := by
  rw [value53, value63, value65, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (280 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 100 = false := by
  rw [value53, value63, value65, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (280 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 53 = false ∨ valuation q 66 = false ∨ valuation q 81 = false := by
  rw [value53, value65, value66, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (283 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 53 = false ∨ valuation q 66 = false ∨ valuation q 100 = false := by
  rw [value53, value65, value66, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (283 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 81 = false := by
  rw [value63, value65, value66, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (280 : Vertex) (283 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 100 = false := by
  rw [value63, value65, value66, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (280 : Vertex) (283 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 63 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value63, value65, value81, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (280 : Vertex) (346 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 54 = true ∨ valuation q 59 = true ∨ valuation q 64 = true ∨ valuation q 65 = true ∨ valuation q 67 = true := by
  rw [value54, value59, value64, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ∈ [(267 : Vertex), (275 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (283 : Vertex) [(267 : Vertex), (275 : Vertex), (281 : Vertex), (282 : Vertex), (287 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 54 = false ∨ valuation q 59 = false ∨ valuation q 64 = false := by
  rw [value54, value59, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (275 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 54 = false ∨ valuation q 59 = false ∨ valuation q 65 = false := by
  rw [value54, value59, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (275 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value54, value64, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (281 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 54 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value54, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (282 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 54 = true ∨ valuation q 59 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value54, value59, value64, value66, value67, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(267 : Vertex), (275 : Vertex), (281 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (282 : Vertex) [(267 : Vertex), (275 : Vertex), (281 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 183 = true ∨ valuation q 54 = true ∨ valuation q 59 = true ∨ valuation q 64 = true ∨ valuation q 65 = true := by
  rw [value54, value59, value64, value65, value66, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(267 : Vertex), (275 : Vertex), (281 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (287 : Vertex) [(267 : Vertex), (275 : Vertex), (281 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value57, value62, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (279 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 66 = true := by
  rw [value57, value66, value67, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(271 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(271 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 45 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value45, value68, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (256 : Vertex) (321 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 185 = true ∨ valuation q 69 = true ∨ valuation q 72 = true := by
  rw [value68, value69, value72, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (256 : Vertex) → w ∈ [(321 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (256 : Vertex) [(321 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 185 = true ∨ valuation q 45 = true ∨ valuation q 72 = true := by
  rw [value45, value68, value72, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(256 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(256 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 185 = true ∨ valuation q 45 = true ∨ valuation q 69 = true := by
  rw [value45, value68, value69, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(256 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(256 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 186 = true ∨ valuation q 46 = true ∨ valuation q 73 = true ∨ valuation q 77 = true := by
  rw [value46, value69, value73, value77, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(257 : Vertex), (329 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(257 : Vertex), (329 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block13 (q : Snake 81) (h : Conditions q) : B112E207.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112207
