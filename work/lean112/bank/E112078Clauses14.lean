import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 24 = false ∨ valuation q 62 = false ∨ valuation q 85 = false := by
  rw [value24, value62, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (136 : Vertex) (264 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 209 = true ∨ valuation q 24 = true ∨ valuation q 85 = true ∨ valuation q 91 = true := by
  rw [value24, value85, value90, value91, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(136 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (264 : Vertex) [(136 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value25, value86, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 86 = false ∨ valuation q 92 = false := by
  rw [value25, value86, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 86 = false ∨ valuation q 106 = false := by
  rw [value25, value86, value91, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value25, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 90 = false ∨ valuation q 106 = false := by
  rw [value25, value90, value91, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 92 = false ∨ valuation q 106 = false := by
  rw [value25, value91, value92, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (397 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value86, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 106 = false := by
  rw [value86, value90, value91, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (385 : Vertex) (392 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 106 = false := by
  rw [value90, value91, value92, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (392 : Vertex) (397 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value87, value91, value92, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 211 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 100 = true := by
  rw [value87, value91, value92, value100, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (399 : Vertex) [(389 : Vertex), (393 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 211 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 93 = true := by
  rw [value87, value91, value92, value93, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (393 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(389 : Vertex), (393 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 212 = true ∨ valuation q 92 = true := by
  rw [value92, value93, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(397 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 212 = true ∨ valuation q 89 = true := by
  rw [value89, value93, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(391 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (397 : Vertex) [(391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 213 = true ∨ valuation q 86 = true := by
  rw [value86, value94, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(385 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 215 = true ∨ valuation q 95 = true := by
  rw [value95, value96, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 215 = true ∨ valuation q 94 = true := by
  rw [value94, value96, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(401 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (402 : Vertex) [(401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 95 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value95, value97, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (402 : Vertex) (414 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 34 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value34, value95, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 218 = true ∨ valuation q 101 = true := by
  rw [value99, value101, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (413 : Vertex) [(414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 218 = true ∨ valuation q 100 = true := by
  rw [value99, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(413 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 219 = true ∨ valuation q 99 = true := by
  rw [value99, value100, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(412 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (397 : Vertex) [(412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 219 = true ∨ valuation q 92 = true := by
  rw [value92, value100, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(397 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (412 : Vertex) [(397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value97, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 39 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value39, value102, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value103, value107, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 221 = true ∨ valuation q 39 = true ∨ valuation q 107 = true := by
  rw [value39, value102, value107, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(194 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(194 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 221 = true ∨ valuation q 39 = true ∨ valuation q 103 = true := by
  rw [value39, value102, value103, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(194 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (458 : Vertex) [(194 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 40 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value40, value102, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (195 : Vertex) (450 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 222 = true ∨ valuation q 102 = true ∨ valuation q 108 = true := by
  rw [value102, value103, value108, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (195 : Vertex) [(450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E078.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112078
