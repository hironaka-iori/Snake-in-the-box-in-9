import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 86 = false ∨ valuation q 94 = false ∨ valuation q 103 = false := by
  rw [value86, value93, value94, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (395 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 86 = false ∨ valuation q 96 = false ∨ valuation q 103 = false := by
  rw [value86, value93, value96, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value91, value93, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (395 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 103 = false := by
  rw [value91, value93, value94, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (395 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 96 = false ∨ valuation q 103 = false := by
  rw [value91, value93, value96, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 103 = false := by
  rw [value93, value94, value96, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (395 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 220 = true ∨ valuation q 86 = true ∨ valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 103 = true := by
  rw [value86, value93, value94, value96, value103, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(386 : Vertex), (395 : Vertex), (398 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (392 : Vertex) [(386 : Vertex), (395 : Vertex), (398 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 220 = true ∨ valuation q 86 = true ∨ valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 96 = true := by
  rw [value86, value91, value93, value94, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(386 : Vertex), (392 : Vertex), (395 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (410 : Vertex) [(386 : Vertex), (392 : Vertex), (395 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 92 = false := by
  rw [value19, value55, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 93 = false := by
  rw [value19, value55, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 104 = false := by
  rw [value19, value55, value94, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 115 = false := by
  rw [value19, value55, value94, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (267 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value19, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (393 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 92 = false ∨ valuation q 104 = false := by
  rw [value19, value92, value94, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (393 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 92 = false ∨ valuation q 115 = false := by
  rw [value19, value92, value94, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (393 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value19, value93, value94, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (394 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 93 = false ∨ valuation q 115 = false := by
  rw [value19, value93, value94, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (394 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 19 = false ∨ valuation q 104 = false ∨ valuation q 115 = false := by
  rw [value19, value94, value104, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (139 : Vertex) (411 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 55 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value55, value93, value94, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (267 : Vertex) (394 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 55 = false ∨ valuation q 93 = false ∨ valuation q 115 = false := by
  rw [value55, value93, value94, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (267 : Vertex) (394 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 55 = false ∨ valuation q 104 = false ∨ valuation q 115 = false := by
  rw [value55, value94, value104, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (267 : Vertex) (411 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 115 = false := by
  rw [value92, value93, value94, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (393 : Vertex) (394 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 104 = false ∨ valuation q 115 = false := by
  rw [value92, value94, value104, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (393 : Vertex) (411 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 115 = false := by
  rw [value93, value94, value104, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (395 : Vertex) (394 : Vertex) (411 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 105 = false := by
  rw [value21, value57, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 21 = false ∨ valuation q 88 = false ∨ valuation q 92 = false := by
  rw [value21, value88, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (389 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 21 = false ∨ valuation q 88 = false ∨ valuation q 105 = false := by
  rw [value21, value88, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (389 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 21 = false ∨ valuation q 88 = false ∨ valuation q 116 = false := by
  rw [value21, value88, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (389 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 21 = false ∨ valuation q 92 = false ∨ valuation q 105 = false := by
  rw [value21, value92, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 21 = false ∨ valuation q 92 = false ∨ valuation q 116 = false := by
  rw [value21, value92, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (393 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 57 = false ∨ valuation q 88 = false ∨ valuation q 105 = false := by
  rw [value57, value88, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (389 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 57 = false ∨ valuation q 88 = false ∨ valuation q 116 = false := by
  rw [value57, value88, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (389 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E052.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112052
