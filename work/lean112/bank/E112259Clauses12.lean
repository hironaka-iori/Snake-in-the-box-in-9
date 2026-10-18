import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value54, value75, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (164 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value54, value75, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (164 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 79 = false ∨ valuation q 103 = false := by
  rw [value54, value75, value79, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (164 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 81 = false ∨ valuation q 86 = false := by
  rw [value54, value75, value81, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 54 = false ∨ valuation q 81 = false ∨ valuation q 103 = false := by
  rw [value54, value75, value81, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (128 : Vertex) (168 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 79 = false ∨ valuation q 81 = false := by
  rw [value75, value76, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (164 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value75, value76, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (164 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 86 = false := by
  rw [value75, value76, value81, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 79 = false ∨ valuation q 103 = false := by
  rw [value75, value77, value79, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (164 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 103 = false := by
  rw [value75, value81, value86, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 191 = true ∨ valuation q 54 = true ∨ valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 86 = true := by
  rw [value54, value75, value76, value77, value79, value81, value86, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(128 : Vertex), (161 : Vertex), (162 : Vertex), (164 : Vertex), (168 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (224 : Vertex) [(128 : Vertex), (161 : Vertex), (162 : Vertex), (164 : Vertex), (168 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 75 = false := by
  rw [value19, value55, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (129 : Vertex) (160 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 78 = false := by
  rw [value19, value55, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (129 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 87 = false := by
  rw [value19, value55, value76, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (129 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 104 = false := by
  rw [value19, value55, value76, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (129 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value19, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (160 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 75 = false ∨ valuation q 87 = false := by
  rw [value19, value75, value76, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (160 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 75 = false ∨ valuation q 104 = false := by
  rw [value19, value75, value76, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (160 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 78 = false ∨ valuation q 87 = false := by
  rw [value19, value76, value78, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (163 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 78 = false ∨ valuation q 104 = false := by
  rw [value19, value76, value78, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (163 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 19 = false ∨ valuation q 87 = false ∨ valuation q 104 = false := by
  rw [value19, value76, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (177 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 55 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value55, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (129 : Vertex) (160 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 55 = false ∨ valuation q 75 = false ∨ valuation q 87 = false := by
  rw [value55, value75, value76, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (129 : Vertex) (160 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 55 = false ∨ valuation q 75 = false ∨ valuation q 104 = false := by
  rw [value55, value75, value76, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (129 : Vertex) (160 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 55 = false ∨ valuation q 78 = false ∨ valuation q 87 = false := by
  rw [value55, value76, value78, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (129 : Vertex) (163 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 55 = false ∨ valuation q 78 = false ∨ valuation q 104 = false := by
  rw [value55, value76, value78, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (129 : Vertex) (163 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 55 = false ∨ valuation q 87 = false ∨ valuation q 104 = false := by
  rw [value55, value76, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (129 : Vertex) (177 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 87 = false := by
  rw [value75, value76, value78, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (163 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 104 = false := by
  rw [value75, value76, value78, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (163 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 87 = false ∨ valuation q 104 = false := by
  rw [value75, value76, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (177 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 87 = false ∨ valuation q 104 = false := by
  rw [value76, value78, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (163 : Vertex) (177 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 192 = true ∨ valuation q 55 = true ∨ valuation q 75 = true ∨ valuation q 78 = true ∨ valuation q 87 = true ∨ valuation q 104 = true := by
  rw [value55, value75, value76, value78, value87, value104, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(129 : Vertex), (160 : Vertex), (163 : Vertex), (177 : Vertex), (225 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (33 : Vertex) [(129 : Vertex), (160 : Vertex), (163 : Vertex), (177 : Vertex), (225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E259.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112259
