import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 57 = false ∨ valuation q 73 = false := by
  rw [value39, value57, value60, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (194 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 57 = false ∨ valuation q 111 = false := by
  rw [value39, value57, value60, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (194 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value39, value60, value61, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (199 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 61 = false ∨ valuation q 73 = false := by
  rw [value39, value60, value61, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 61 = false ∨ valuation q 111 = false := by
  rw [value39, value60, value61, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (199 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value39, value60, value67, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 67 = false ∨ valuation q 111 = false := by
  rw [value39, value60, value67, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (206 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 73 = false ∨ valuation q 111 = false := by
  rw [value39, value60, value73, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (214 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value57, value60, value61, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (199 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 73 = false := by
  rw [value57, value60, value61, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 111 = false := by
  rw [value57, value60, value61, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (199 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value57, value60, value67, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 67 = false ∨ valuation q 111 = false := by
  rw [value57, value60, value67, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (206 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 73 = false ∨ valuation q 111 = false := by
  rw [value57, value60, value73, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (214 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value60, value61, value67, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (199 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 111 = false := by
  rw [value60, value61, value67, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (199 : Vertex) (206 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 73 = false ∨ valuation q 111 = false := by
  rw [value60, value61, value73, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (199 : Vertex) (214 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 67 = false ∨ valuation q 73 = false ∨ valuation q 111 = false := by
  rw [value60, value67, value73, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (206 : Vertex) (214 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 61 = true := by
  rw [value61, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (199 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 68 = true := by
  rw [value58, value59, value60, value61, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ∈ [(195 : Vertex), (197 : Vertex), (198 : Vertex), (207 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (199 : Vertex) [(195 : Vertex), (197 : Vertex), (198 : Vertex), (207 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value58, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (195 : Vertex) (197 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 60 = false ∨ valuation q 68 = false := by
  rw [value60, value68, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (199 : Vertex) (198 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 68 = true := by
  rw [value59, value60, value61, value68, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(197 : Vertex), (198 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (195 : Vertex) [(197 : Vertex), (198 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 68 = true := by
  rw [value58, value60, value61, value68, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(195 : Vertex), (198 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (197 : Vertex) [(195 : Vertex), (198 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 68 = true := by
  rw [value58, value59, value61, value68, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(195 : Vertex), (197 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (198 : Vertex) [(195 : Vertex), (197 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value58, value59, value60, value61, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(195 : Vertex), (197 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(195 : Vertex), (197 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 62 = true := by
  rw [value62, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (200 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 23 = false ∨ valuation q 40 = false ∨ valuation q 63 = false := by
  rw [value23, value40, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (136 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 23 = false ∨ valuation q 40 = false ∨ valuation q 65 = false := by
  rw [value23, value40, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (136 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 23 = false ∨ valuation q 40 = false ∨ valuation q 112 = false := by
  rw [value23, value40, value62, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (136 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 23 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value23, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (201 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 23 = false ∨ valuation q 63 = false ∨ valuation q 74 = false := by
  rw [value23, value62, value63, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (201 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E089.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112089
