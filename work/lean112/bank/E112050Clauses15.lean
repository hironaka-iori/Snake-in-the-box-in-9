import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 115 = false := by
  rw [value93, value95, value96, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (395 : Vertex) (397 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 103 = false ∨ valuation q 115 = false := by
  rw [value93, value95, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (395 : Vertex) (409 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 103 = false ∨ valuation q 115 = false := by
  rw [value93, value96, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (397 : Vertex) (409 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 221 = true ∨ valuation q 54 = true ∨ valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 96 = true ∨ valuation q 103 = true ∨ valuation q 115 = true := by
  rw [value54, value92, value93, value95, value96, value103, value115, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(265 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex), (409 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (137 : Vertex) [(265 : Vertex), (392 : Vertex), (395 : Vertex), (397 : Vertex), (409 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value87, value92, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value87, value92, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 87 = false ∨ valuation q 92 = false ∨ valuation q 104 = false := by
  rw [value87, value92, value94, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value87, value94, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 104 = false := by
  rw [value87, value94, value95, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (395 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 104 = false := by
  rw [value87, value94, value97, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value92, value94, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 104 = false := by
  rw [value92, value94, value95, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (395 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 104 = false := by
  rw [value92, value94, value97, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 104 = false := by
  rw [value94, value95, value97, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (395 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 222 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 104 = true := by
  rw [value87, value94, value95, value97, value104, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(386 : Vertex), (395 : Vertex), (398 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (392 : Vertex) [(386 : Vertex), (395 : Vertex), (398 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 222 = true ∨ valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 97 = true := by
  rw [value87, value92, value94, value95, value97, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(386 : Vertex), (392 : Vertex), (395 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (410 : Vertex) [(386 : Vertex), (392 : Vertex), (395 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 94 = false := by
  rw [value20, value55, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 105 = false := by
  rw [value20, value55, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 20 = false ∨ valuation q 55 = false ∨ valuation q 116 = false := by
  rw [value20, value55, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 20 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value20, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (393 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 20 = false ∨ valuation q 93 = false ∨ valuation q 105 = false := by
  rw [value20, value93, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (393 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 20 = false ∨ valuation q 93 = false ∨ valuation q 116 = false := by
  rw [value20, value93, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (393 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 20 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value20, value94, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (394 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 20 = false ∨ valuation q 94 = false ∨ valuation q 116 = false := by
  rw [value20, value94, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (394 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value93, value94, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (393 : Vertex) (394 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 116 = false := by
  rw [value93, value94, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (393 : Vertex) (394 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 105 = false ∨ valuation q 116 = false := by
  rw [value94, value95, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (394 : Vertex) (411 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 57 = false ∨ valuation q 89 = false := by
  rw [value22, value57, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 57 = false ∨ valuation q 93 = false := by
  rw [value22, value57, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 89 = false ∨ valuation q 117 = false := by
  rw [value22, value89, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (389 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 93 = false ∨ valuation q 106 = false := by
  rw [value22, value93, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 93 = false ∨ valuation q 117 = false := by
  rw [value22, value93, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (393 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E050.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112050
