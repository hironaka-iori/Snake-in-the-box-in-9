import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 81 = false ∨ valuation q 87 = false := by
  rw [value28, value81, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value28, value81, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (386 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value28, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value28, value85, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 28 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value28, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (138 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 58 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value58, value81, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 58 = false ∨ valuation q 81 = false ∨ valuation q 87 = false := by
  rw [value58, value81, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 58 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value58, value81, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 58 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value58, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 58 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value58, value85, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 58 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value58, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value81, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value81, value85, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 81 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value81, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value85, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 29 = true ∨ valuation q 86 = true ∨ valuation q 96 = true ∨ valuation q 106 = true := by
  rw [value29, value86, value87, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ∈ [(139 : Vertex), (394 : Vertex), (411 : Vertex), (459 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (395 : Vertex) [(139 : Vertex), (394 : Vertex), (411 : Vertex), (459 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 208 = true ∨ valuation q 86 = true ∨ valuation q 96 = true ∨ valuation q 106 = true := by
  rw [value86, value87, value96, value106, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(394 : Vertex), (411 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (139 : Vertex) [(394 : Vertex), (411 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 208 = true ∨ valuation q 29 = true ∨ valuation q 96 = true ∨ valuation q 106 = true := by
  rw [value29, value87, value96, value106, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(139 : Vertex), (411 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (394 : Vertex) [(139 : Vertex), (411 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 208 = true ∨ valuation q 29 = true ∨ valuation q 86 = true ∨ valuation q 106 = true := by
  rw [value29, value86, value87, value106, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(139 : Vertex), (394 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (411 : Vertex) [(139 : Vertex), (394 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 208 = true ∨ valuation q 29 = true ∨ valuation q 86 = true ∨ valuation q 96 = true := by
  rw [value29, value86, value87, value96, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (395 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(139 : Vertex), (394 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (395 : Vertex) (459 : Vertex) [(139 : Vertex), (394 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value82, value85, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 107 = false := by
  rw [value82, value85, value88, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 82 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value82, value88, value89, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value85, value88, value89, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (392 : Vertex) (398 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 209 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 107 = true := by
  rw [value85, value88, value89, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(392 : Vertex), (398 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (388 : Vertex) [(392 : Vertex), (398 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 209 = true ∨ valuation q 82 = true ∨ valuation q 89 = true ∨ valuation q 107 = true := by
  rw [value82, value88, value89, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(388 : Vertex), (398 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (392 : Vertex) [(388 : Vertex), (398 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 209 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 107 = true := by
  rw [value82, value85, value88, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(388 : Vertex), (392 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (398 : Vertex) [(388 : Vertex), (392 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 89 = true := by
  rw [value89, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (398 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 109 = true := by
  rw [value84, value86, value88, value89, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ∈ [(390 : Vertex), (394 : Vertex), (396 : Vertex), (462 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (398 : Vertex) [(390 : Vertex), (394 : Vertex), (396 : Vertex), (462 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value84, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (390 : Vertex) (394 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 109 = false := by
  rw [value84, value86, value89, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (390 : Vertex) (394 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value84, value86, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (398 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E019.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112019
