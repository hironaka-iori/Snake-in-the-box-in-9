import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 179 = true ∨ valuation q 45 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 100 = true := by
  rw [value45, value52, value53, value55, value100, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex), (179 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (49 : Vertex) [(161 : Vertex), (176 : Vertex), (179 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 179 = true ∨ valuation q 20 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 100 = true := by
  rw [value20, value52, value53, value55, value100, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(49 : Vertex), (176 : Vertex), (179 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (161 : Vertex) [(49 : Vertex), (176 : Vertex), (179 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 179 = true ∨ valuation q 20 = true ∨ valuation q 45 = true ∨ valuation q 55 = true ∨ valuation q 100 = true := by
  rw [value20, value45, value53, value55, value100, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(49 : Vertex), (161 : Vertex), (179 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (176 : Vertex) [(49 : Vertex), (161 : Vertex), (179 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 179 = true ∨ valuation q 20 = true ∨ valuation q 45 = true ∨ valuation q 52 = true ∨ valuation q 100 = true := by
  rw [value20, value45, value52, value53, value100, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(49 : Vertex), (161 : Vertex), (176 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (179 : Vertex) [(49 : Vertex), (161 : Vertex), (176 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 179 = true ∨ valuation q 20 = true ∨ valuation q 45 = true ∨ valuation q 52 = true ∨ valuation q 55 = true := by
  rw [value20, value45, value52, value53, value55, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(49 : Vertex), (161 : Vertex), (176 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (433 : Vertex) [(49 : Vertex), (161 : Vertex), (176 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 21 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value21, value52, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (50 : Vertex) (176 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 21 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value21, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (50 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 180 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 56 = true := by
  rw [value52, value54, value55, value56, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(176 : Vertex), (179 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (50 : Vertex) [(176 : Vertex), (179 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 180 = true ∨ valuation q 21 = true ∨ valuation q 55 = true ∨ valuation q 56 = true := by
  rw [value21, value54, value55, value56, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(50 : Vertex), (179 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (176 : Vertex) [(50 : Vertex), (179 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 180 = true ∨ valuation q 21 = true ∨ valuation q 52 = true ∨ valuation q 56 = true := by
  rw [value21, value52, value54, value56, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(50 : Vertex), (176 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (179 : Vertex) [(50 : Vertex), (176 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 180 = true ∨ valuation q 21 = true ∨ valuation q 52 = true ∨ valuation q 55 = true := by
  rw [value21, value52, value54, value55, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(50 : Vertex), (176 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (182 : Vertex) [(50 : Vertex), (176 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 22 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value22, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (51 : Vertex) (177 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 22 = false ∨ valuation q 53 = false ∨ valuation q 101 = false := by
  rw [value22, value53, value55, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (51 : Vertex) (177 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 22 = false ∨ valuation q 54 = false ∨ valuation q 101 = false := by
  rw [value22, value54, value55, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (51 : Vertex) (178 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 101 = false := by
  rw [value53, value54, value55, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (177 : Vertex) (178 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 181 = true ∨ valuation q 22 = true ∨ valuation q 54 = true ∨ valuation q 101 = true := by
  rw [value22, value54, value55, value101, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(51 : Vertex), (178 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (177 : Vertex) [(51 : Vertex), (178 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 181 = true ∨ valuation q 22 = true ∨ valuation q 53 = true ∨ valuation q 101 = true := by
  rw [value22, value53, value55, value101, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(51 : Vertex), (177 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (178 : Vertex) [(51 : Vertex), (177 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 25 = false ∨ valuation q 47 = false ∨ valuation q 54 = false := by
  rw [value25, value47, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (54 : Vertex) (166 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 25 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value25, value47, value56, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (54 : Vertex) (166 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value25, value54, value56, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (54 : Vertex) (178 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 47 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value47, value54, value56, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (166 : Vertex) (178 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value47, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (182 : Vertex) (166 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value54, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (182 : Vertex) (178 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 182 = true ∨ valuation q 25 = true ∨ valuation q 54 = true ∨ valuation q 60 = true := by
  rw [value25, value54, value56, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(54 : Vertex), (178 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (166 : Vertex) [(54 : Vertex), (178 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 182 = true ∨ valuation q 25 = true ∨ valuation q 47 = true ∨ valuation q 60 = true := by
  rw [value25, value47, value56, value60, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(54 : Vertex), (166 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (178 : Vertex) [(54 : Vertex), (166 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 48 = false ∨ valuation q 58 = false ∨ valuation q 65 = false := by
  rw [value48, value57, value58, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 48 = false ∨ valuation q 58 = false ∨ valuation q 105 = false := by
  rw [value48, value57, value58, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 183 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 65 = true ∨ valuation q 105 = true := by
  rw [value48, value52, value57, value65, value105, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(168 : Vertex), (176 : Vertex), (248 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (188 : Vertex) [(168 : Vertex), (176 : Vertex), (248 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value57, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (184 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 60 = true := by
  rw [value57, value58, value60, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(184 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(184 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 185 = true ∨ valuation q 58 = true ∨ valuation q 61 = true := by
  rw [value58, value59, value61, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 185 = true ∨ valuation q 50 = true ∨ valuation q 61 = true := by
  rw [value50, value59, value61, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(173 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (188 : Vertex) [(173 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E121.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112121
