import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 49 = false ∨ valuation q 72 = false ∨ valuation q 113 = false := by
  rw [value49, value70, value72, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (148 : Vertex) (220 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 66 = false ∨ valuation q 72 = false ∨ valuation q 113 = false := by
  rw [value66, value70, value72, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (208 : Vertex) (220 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 73 = false := by
  rw [value52, value68, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 114 = false := by
  rw [value52, value68, value71, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 52 = false ∨ valuation q 73 = false ∨ valuation q 114 = false := by
  rw [value52, value71, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (222 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 68 = false ∨ valuation q 73 = false ∨ valuation q 114 = false := by
  rw [value68, value71, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (210 : Vertex) (222 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 62 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value62, value70, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (204 : Vertex) (212 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value70, value72, value73, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(212 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (204 : Vertex) [(212 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 189 = true ∨ valuation q 62 = true ∨ valuation q 70 = true := by
  rw [value62, value70, value72, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(204 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (222 : Vertex) [(204 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 190 = true ∨ valuation q 64 = true ∨ valuation q 72 = true := by
  rw [value64, value72, value73, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(206 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (218 : Vertex) [(206 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 190 = true ∨ valuation q 64 = true ∨ valuation q 71 = true := by
  rw [value64, value71, value73, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(206 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (220 : Vertex) [(206 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 76 = true ∨ valuation q 80 = true := by
  rw [value74, value76, value80, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (1 : Vertex) [(261 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 2 = true ∨ valuation q 80 = true := by
  rw [value2, value74, value80, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(1 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(1 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 191 = true ∨ valuation q 2 = true ∨ valuation q 76 = true := by
  rw [value2, value74, value76, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(1 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (265 : Vertex) [(1 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 192 = true ∨ valuation q 76 = true ∨ valuation q 85 = true := by
  rw [value75, value76, value85, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(261 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (262 : Vertex) [(261 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 192 = true ∨ valuation q 76 = true ∨ valuation q 77 = true := by
  rw [value75, value76, value77, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (276 : Vertex) [(261 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value74, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (260 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 86 = false := by
  rw [value74, value75, value76, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (260 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value74, value76, value78, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (263 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value75, value76, value78, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (263 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = true ∨ valuation q 78 = true ∨ valuation q 82 = true := by
  rw [value75, value77, value78, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ∈ [(260 : Vertex), (263 : Vertex), (270 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (262 : Vertex) [(260 : Vertex), (263 : Vertex), (270 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 82 = false := by
  rw [value75, value77, value78, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (263 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 194 = true ∨ valuation q 75 = true ∨ valuation q 82 = true := by
  rw [value75, value77, value82, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(260 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (263 : Vertex) [(260 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 194 = true ∨ valuation q 75 = true ∨ valuation q 78 = true := by
  rw [value75, value77, value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (270 : Vertex) [(260 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 5 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value5, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (7 : Vertex) (261 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 76 = true ∨ valuation q 77 = true := by
  rw [value76, value77, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (7 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (7 : Vertex) [(261 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 5 = true ∨ valuation q 77 = true := by
  rw [value5, value77, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(7 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (261 : Vertex) [(7 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 195 = true ∨ valuation q 5 = true ∨ valuation q 76 = true := by
  rw [value5, value76, value78, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(7 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (262 : Vertex) [(7 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 6 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value6, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (265 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 6 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value6, value79, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (265 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 7 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value7, value74, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (9 : Vertex) (257 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 197 = true ∨ valuation q 7 = true ∨ valuation q 79 = true := by
  rw [value7, value79, value80, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(9 : Vertex), (264 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (257 : Vertex) [(9 : Vertex), (264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E115.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112115
