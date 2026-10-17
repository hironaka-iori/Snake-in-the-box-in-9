import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value94, value95, value106, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (428 : Vertex) (429 : Vertex) (444 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value90, value94, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (421 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 94 = true ∨ valuation q 97 = true := by
  rw [value94, value95, value97, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(428 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (421 : Vertex) [(428 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value90, value94, value95, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(421 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (431 : Vertex) [(421 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 77 = false ∨ valuation q 94 = false := by
  rw [value42, value77, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (302 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 77 = false ∨ valuation q 97 = false := by
  rw [value42, value77, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (302 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 77 = false ∨ valuation q 107 = false := by
  rw [value42, value77, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (302 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 77 = false ∨ valuation q 116 = false := by
  rw [value42, value77, value96, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (302 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value42, value94, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 94 = false ∨ valuation q 107 = false := by
  rw [value42, value94, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (428 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 94 = false ∨ valuation q 116 = false := by
  rw [value42, value94, value96, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (428 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value42, value96, value97, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (431 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 97 = false ∨ valuation q 116 = false := by
  rw [value42, value96, value97, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (431 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 42 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value42, value96, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (446 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value77, value94, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 107 = false := by
  rw [value77, value94, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (428 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 116 = false := by
  rw [value77, value94, value96, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (428 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value77, value96, value97, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (431 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 97 = false ∨ valuation q 116 = false := by
  rw [value77, value96, value97, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (431 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 77 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value77, value96, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (446 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value94, value96, value97, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (428 : Vertex) (431 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 116 = false := by
  rw [value94, value96, value97, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (428 : Vertex) (431 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value94, value96, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (428 : Vertex) (446 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 107 = false ∨ valuation q 116 = false := by
  rw [value96, value97, value107, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (431 : Vertex) (446 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value91, value93, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value93, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (429 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 108 = false := by
  rw [value93, value95, value97, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (429 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 93 = true ∨ valuation q 95 = true ∨ valuation q 96 = true ∨ valuation q 108 = true := by
  rw [value93, value95, value96, value97, value108, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(427 : Vertex), (429 : Vertex), (430 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (423 : Vertex) [(427 : Vertex), (429 : Vertex), (430 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 91 = true ∨ valuation q 95 = true ∨ valuation q 96 = true ∨ valuation q 108 = true := by
  rw [value91, value95, value96, value97, value108, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(423 : Vertex), (429 : Vertex), (430 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (427 : Vertex) [(423 : Vertex), (429 : Vertex), (430 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 96 = true ∨ valuation q 108 = true := by
  rw [value91, value93, value96, value97, value108, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (429 : Vertex) → w ∈ [(423 : Vertex), (427 : Vertex), (430 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (429 : Vertex) [(423 : Vertex), (427 : Vertex), (430 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 95 = true ∨ valuation q 108 = true := by
  rw [value91, value93, value95, value97, value108, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(423 : Vertex), (427 : Vertex), (429 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (430 : Vertex) [(423 : Vertex), (427 : Vertex), (429 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 95 = true ∨ valuation q 96 = true := by
  rw [value91, value93, value95, value96, value97, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(423 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (447 : Vertex) [(423 : Vertex), (427 : Vertex), (429 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E008.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112008
