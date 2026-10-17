import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 16 = false ∨ valuation q 51 = false ∨ valuation q 101 = false := by
  rw [value16, value51, value82, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (258 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 16 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value16, value80, value82, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (384 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 16 = false ∨ valuation q 80 = false ∨ valuation q 94 = false := by
  rw [value16, value80, value82, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (384 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 16 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value16, value80, value82, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (384 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 16 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value16, value82, value87, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (394 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 16 = false ∨ valuation q 87 = false ∨ valuation q 101 = false := by
  rw [value16, value82, value87, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (394 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value51, value80, value82, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 94 = false := by
  rw [value51, value80, value82, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value51, value80, value82, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value51, value82, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (387 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 83 = false ∨ valuation q 101 = false := by
  rw [value51, value82, value83, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (387 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 51 = false ∨ valuation q 94 = false ∨ valuation q 101 = false := by
  rw [value51, value82, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (402 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value80, value82, value87, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (394 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 101 = false := by
  rw [value80, value82, value87, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (394 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 94 = false ∨ valuation q 101 = false := by
  rw [value80, value82, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (402 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 94 = false ∨ valuation q 101 = false := by
  rw [value82, value87, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (394 : Vertex) (402 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value83, value87, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (386 : Vertex) (387 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 83 = false ∨ valuation q 101 = false := by
  rw [value83, value101, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (386 : Vertex) (387 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 200 = true ∨ valuation q 51 = true ∨ valuation q 80 = true ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 94 = true ∨ valuation q 101 = true := by
  rw [value51, value80, value82, value83, value87, value94, value101, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (387 : Vertex), (394 : Vertex), (402 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (130 : Vertex) [(258 : Vertex), (384 : Vertex), (387 : Vertex), (394 : Vertex), (402 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 200 = true ∨ valuation q 16 = true ∨ valuation q 51 = true ∨ valuation q 80 = true ∨ valuation q 83 = true ∨ valuation q 94 = true ∨ valuation q 101 = true := by
  rw [value16, value51, value80, value82, value83, value94, value101, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (402 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (402 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 200 = true ∨ valuation q 16 = true ∨ valuation q 51 = true ∨ valuation q 80 = true ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 94 = true := by
  rw [value16, value51, value80, value82, value83, value87, value94, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (394 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (450 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (394 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 81 = false := by
  rw [value17, value52, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 82 = false := by
  rw [value17, value52, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value17, value52, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 95 = false := by
  rw [value17, value52, value83, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 102 = false := by
  rw [value17, value52, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value17, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (385 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value17, value81, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (385 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 81 = false ∨ valuation q 95 = false := by
  rw [value17, value81, value83, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (385 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value17, value81, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (385 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value17, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 17 = false ∨ valuation q 82 = false ∨ valuation q 95 = false := by
  rw [value17, value82, value83, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E027.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112027
