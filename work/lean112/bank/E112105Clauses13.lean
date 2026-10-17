import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 67 = true ∨ valuation q 80 = true := by
  rw [value67, value72, value80, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(320 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (329 : Vertex) [(320 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 67 = true ∨ valuation q 73 = true := by
  rw [value67, value72, value73, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (344 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 16 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value16, value72, value73, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (328 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 16 = false ∨ valuation q 72 = false ∨ valuation q 108 = false := by
  rw [value16, value72, value73, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (328 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 16 = false ∨ valuation q 81 = false ∨ valuation q 108 = false := by
  rw [value16, value73, value81, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (73 : Vertex) (345 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 108 = false := by
  rw [value72, value73, value81, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (328 : Vertex) (345 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 74 = true := by
  rw [value74, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (334 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 19 = true ∨ valuation q 70 = true ∨ valuation q 75 = true ∨ valuation q 112 = true := by
  rw [value19, value70, value74, value75, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ∈ [(78 : Vertex), (326 : Vertex), (335 : Vertex), (462 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (334 : Vertex) [(78 : Vertex), (326 : Vertex), (335 : Vertex), (462 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 19 = false ∨ valuation q 70 = false ∨ valuation q 75 = false := by
  rw [value19, value70, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (78 : Vertex) (326 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 19 = false ∨ valuation q 70 = false := by
  rw [value19, value70, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (334 : Vertex) (78 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 70 = true ∨ valuation q 75 = true ∨ valuation q 112 = true := by
  rw [value70, value74, value75, value112, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(326 : Vertex), (335 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (78 : Vertex) [(326 : Vertex), (335 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 19 = true ∨ valuation q 75 = true ∨ valuation q 112 = true := by
  rw [value19, value74, value75, value112, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(78 : Vertex), (335 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (326 : Vertex) [(78 : Vertex), (335 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 19 = true ∨ valuation q 70 = true ∨ valuation q 112 = true := by
  rw [value19, value70, value74, value112, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(78 : Vertex), (326 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (335 : Vertex) [(78 : Vertex), (326 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 19 = true ∨ valuation q 70 = true ∨ valuation q 75 = true := by
  rw [value19, value70, value74, value75, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(78 : Vertex), (326 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (462 : Vertex) [(78 : Vertex), (326 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 20 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value20, value71, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (79 : Vertex) (327 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 20 = false ∨ valuation q 74 = false ∨ valuation q 113 = false := by
  rw [value20, value74, value75, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (79 : Vertex) (334 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 113 = false := by
  rw [value71, value74, value75, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (335 : Vertex) (327 : Vertex) (334 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 20 = true ∨ valuation q 74 = true ∨ valuation q 113 = true := by
  rw [value20, value74, value75, value113, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(79 : Vertex), (334 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (327 : Vertex) [(79 : Vertex), (334 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 20 = true ∨ valuation q 71 = true ∨ valuation q 113 = true := by
  rw [value20, value71, value75, value113, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(79 : Vertex), (327 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (334 : Vertex) [(79 : Vertex), (327 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 24 = true ∨ valuation q 79 = true ∨ valuation q 82 = true := by
  rw [value24, value76, value79, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ∈ [(83 : Vertex), (343 : Vertex), (347 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (339 : Vertex) [(83 : Vertex), (343 : Vertex), (347 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 24 = false ∨ valuation q 79 = false ∨ valuation q 82 = false := by
  rw [value24, value76, value79, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (339 : Vertex) (83 : Vertex) (343 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 79 = true ∨ valuation q 82 = true := by
  rw [value76, value79, value82, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(343 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (83 : Vertex) [(343 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 24 = true ∨ valuation q 82 = true := by
  rw [value24, value76, value82, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(83 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (343 : Vertex) [(83 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 24 = true ∨ valuation q 79 = true := by
  rw [value24, value76, value79, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(83 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (347 : Vertex) [(83 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 25 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value25, value77, value78, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (341 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 25 = false ∨ valuation q 78 = false ∨ valuation q 117 = false := by
  rw [value25, value77, value78, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (341 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 25 = false ∨ valuation q 83 = false ∨ valuation q 117 = false := by
  rw [value25, value77, value83, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (84 : Vertex) (348 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 117 = false := by
  rw [value77, value78, value83, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (340 : Vertex) (341 : Vertex) (348 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 78 = true ∨ valuation q 83 = true ∨ valuation q 117 = true := by
  rw [value77, value78, value83, value117, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(341 : Vertex), (348 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (84 : Vertex) [(341 : Vertex), (348 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 25 = true ∨ valuation q 83 = true ∨ valuation q 117 = true := by
  rw [value25, value77, value83, value117, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(84 : Vertex), (348 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (341 : Vertex) [(84 : Vertex), (348 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 25 = true ∨ valuation q 78 = true ∨ valuation q 117 = true := by
  rw [value25, value77, value78, value117, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(84 : Vertex), (341 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (348 : Vertex) [(84 : Vertex), (341 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 25 = true ∨ valuation q 78 = true ∨ valuation q 83 = true := by
  rw [value25, value77, value78, value83, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (340 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(84 : Vertex), (341 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (340 : Vertex) (468 : Vertex) [(84 : Vertex), (341 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block13 (q : Snake 81) (h : Conditions q) : B112E105.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112105
