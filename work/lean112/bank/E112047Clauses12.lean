import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 16 = false ∨ valuation q 83 = false ∨ valuation q 100 = false := by
  rw [value16, value80, value83, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (390 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 50 = false ∨ valuation q 79 = false ∨ valuation q 83 = false := by
  rw [value50, value79, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 50 = false ∨ valuation q 79 = false ∨ valuation q 87 = false := by
  rw [value50, value79, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (384 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 50 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value50, value80, value81, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (387 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 50 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value50, value80, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 50 = false ∨ valuation q 83 = false ∨ valuation q 100 = false := by
  rw [value50, value80, value83, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (390 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 50 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value50, value80, value87, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (258 : Vertex) (394 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 87 = false := by
  rw [value79, value80, value81, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (387 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value80, value81, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (387 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 198 = true ∨ valuation q 50 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 100 = true := by
  rw [value50, value79, value80, value81, value83, value87, value100, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (130 : Vertex) [(258 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 198 = true ∨ valuation q 16 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 100 = true := by
  rw [value16, value79, value80, value81, value83, value87, value100, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(130 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (258 : Vertex) [(130 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 198 = true ∨ valuation q 16 = true ∨ valuation q 50 = true ∨ valuation q 79 = true ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 100 = true := by
  rw [value16, value50, value79, value80, value83, value87, value100, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (387 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 198 = true ∨ valuation q 16 = true ∨ valuation q 50 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 87 = true := by
  rw [value16, value50, value79, value80, value81, value83, value87, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (450 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (387 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 80 = false := by
  rw [value17, value51, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 84 = false := by
  rw [value17, value51, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 91 = false := by
  rw [value17, value51, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 51 = false ∨ valuation q 101 = false := by
  rw [value17, value51, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value17, value80, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 80 = false ∨ valuation q 91 = false := by
  rw [value17, value80, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value17, value80, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 84 = false ∨ valuation q 91 = false := by
  rw [value17, value81, value84, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 84 = false ∨ valuation q 101 = false := by
  rw [value17, value81, value84, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 17 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value17, value81, value91, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value51, value80, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 91 = false := by
  rw [value51, value80, value81, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 51 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value51, value80, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 51 = false ∨ valuation q 84 = false ∨ valuation q 91 = false := by
  rw [value51, value81, value84, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 51 = false ∨ valuation q 84 = false ∨ valuation q 101 = false := by
  rw [value51, value81, value84, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 51 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value51, value81, value91, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 91 = false := by
  rw [value80, value81, value84, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 101 = false := by
  rw [value80, value81, value84, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value80, value81, value91, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (386 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E047.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112047
