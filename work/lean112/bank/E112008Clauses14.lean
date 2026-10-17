import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 84 = true ∨ valuation q 85 = true := by
  rw [value82, value84, value85, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(315 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (297 : Vertex) [(315 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 75 = true ∨ valuation q 85 = true := by
  rw [value75, value82, value85, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(297 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (315 : Vertex) [(297 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 75 = true ∨ valuation q 84 = true := by
  rw [value75, value82, value84, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(297 : Vertex), (315 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (317 : Vertex) [(297 : Vertex), (315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 15 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value15, value78, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (314 : Vertex) (58 : Vertex) (306 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 78 = true ∨ valuation q 84 = true ∨ valuation q 104 = true := by
  rw [value78, value83, value84, value104, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(306 : Vertex), (315 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (58 : Vertex) [(306 : Vertex), (315 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 15 = true ∨ valuation q 84 = true ∨ valuation q 104 = true := by
  rw [value15, value83, value84, value104, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(58 : Vertex), (315 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (306 : Vertex) [(58 : Vertex), (315 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 15 = true ∨ valuation q 78 = true ∨ valuation q 104 = true := by
  rw [value15, value78, value83, value104, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(58 : Vertex), (306 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (315 : Vertex) [(58 : Vertex), (306 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 15 = true ∨ valuation q 78 = true ∨ valuation q 84 = true := by
  rw [value15, value78, value83, value84, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(58 : Vertex), (306 : Vertex), (315 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (442 : Vertex) [(58 : Vertex), (306 : Vertex), (315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 105 = false := by
  rw [value82, value83, value84, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (315 : Vertex) (313 : Vertex) (314 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 83 = true ∨ valuation q 105 = true := by
  rw [value83, value84, value105, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (313 : Vertex) → w ∈ [(314 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (313 : Vertex) [(314 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 82 = true ∨ valuation q 105 = true := by
  rw [value82, value84, value105, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(313 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (314 : Vertex) [(313 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 82 = true := by
  rw [value82, value85, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (309 : Vertex) → w ∈ [(313 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (309 : Vertex) [(313 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 80 = true := by
  rw [value80, value85, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (317 : Vertex) w → w ∈ region → w ≠ (313 : Vertex) → w ∈ [(309 : Vertex)] := by decide
  have hg := other_cover q (317 : Vertex) (313 : Vertex) [(309 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 32 = false ∨ valuation q 70 = false ∨ valuation q 87 = false := by
  rw [value32, value70, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 32 = false ∨ valuation q 70 = false ∨ valuation q 98 = false := by
  rw [value32, value70, value86, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (288 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 32 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value32, value86, value87, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 32 = false ∨ valuation q 87 = false ∨ valuation q 98 = false := by
  rw [value32, value86, value87, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 32 = false ∨ valuation q 87 = false ∨ valuation q 109 = false := by
  rw [value32, value86, value87, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (417 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 32 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value32, value86, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (432 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 70 = false ∨ valuation q 87 = false ∨ valuation q 109 = false := by
  rw [value70, value86, value87, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (417 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 70 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value70, value86, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (288 : Vertex) (432 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value86, value87, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (417 : Vertex) (432 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value86, value88, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (418 : Vertex) (432 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 210 = true ∨ valuation q 32 = true ∨ valuation q 70 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 92 = true ∨ valuation q 98 = true := by
  rw [value32, value70, value86, value87, value88, value92, value98, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(160 : Vertex), (288 : Vertex), (417 : Vertex), (418 : Vertex), (424 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (480 : Vertex) [(160 : Vertex), (288 : Vertex), (417 : Vertex), (418 : Vertex), (424 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 86 = false := by
  rw [value33, value71, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value33, value71, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 90 = false := by
  rw [value33, value71, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 99 = false := by
  rw [value33, value71, value87, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 110 = false := by
  rw [value33, value71, value87, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (289 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value33, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value33, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 33 = false ∨ valuation q 86 = false ∨ valuation q 99 = false := by
  rw [value33, value86, value87, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (416 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E008.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112008
