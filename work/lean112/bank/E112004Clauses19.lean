import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 100 = false := by
  rw [value91, value92, value93, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (427 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 211 = true ∨ valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 100 = true := by
  rw [value91, value92, value93, value100, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(427 : Vertex), (430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (424 : Vertex) [(427 : Vertex), (430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 211 = true ∨ valuation q 89 = true ∨ valuation q 93 = true ∨ valuation q 100 = true := by
  rw [value89, value91, value93, value100, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(424 : Vertex), (430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (427 : Vertex) [(424 : Vertex), (430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 211 = true ∨ valuation q 89 = true ∨ valuation q 92 = true ∨ valuation q 100 = true := by
  rw [value89, value91, value92, value100, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(424 : Vertex), (427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(424 : Vertex), (427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 40 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value40, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (425 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 40 = false ∨ valuation q 90 = false ∨ valuation q 101 = false := by
  rw [value40, value90, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (425 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 40 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value40, value91, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value90, value91, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (425 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 40 = false ∨ valuation q 90 = false := by
  rw [value40, value90, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (427 : Vertex) (171 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 212 = true ∨ valuation q 40 = true ∨ valuation q 91 = true ∨ valuation q 101 = true := by
  rw [value40, value91, value92, value101, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(171 : Vertex), (426 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (425 : Vertex) [(171 : Vertex), (426 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 212 = true ∨ valuation q 40 = true ∨ valuation q 90 = true ∨ valuation q 101 = true := by
  rw [value40, value90, value92, value101, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(171 : Vertex), (425 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (426 : Vertex) [(171 : Vertex), (425 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value87, value91, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value87, value91, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 213 = true ∨ valuation q 91 = true ∨ valuation q 103 = true := by
  rw [value91, value93, value103, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(426 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (422 : Vertex) [(426 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 213 = true ∨ valuation q 87 = true ∨ valuation q 103 = true := by
  rw [value87, value93, value103, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(422 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (426 : Vertex) [(422 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 213 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value87, value91, value93, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(422 : Vertex), (426 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (446 : Vertex) [(422 : Vertex), (426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 44 = false ∨ valuation q 84 = false ∨ valuation q 98 = false := by
  rw [value44, value84, value94, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (176 : Vertex) (416 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 44 = false ∨ valuation q 98 = false := by
  rw [value44, value98, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (432 : Vertex) (176 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 214 = true ∨ valuation q 44 = true ∨ valuation q 84 = true := by
  rw [value44, value84, value94, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(176 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (440 : Vertex) [(176 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 46 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value46, value95, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 46 = false ∨ valuation q 97 = false ∨ valuation q 114 = false := by
  rw [value46, value95, value97, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 46 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value46, value95, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 114 = false := by
  rw [value95, value97, value101, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 215 = true ∨ valuation q 46 = true ∨ valuation q 101 = true ∨ valuation q 114 = true := by
  rw [value46, value95, value101, value114, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(179 : Vertex), (443 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (439 : Vertex) [(179 : Vertex), (443 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 97 = false ∨ valuation q 102 = false := by
  rw [value86, value96, value97, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (439 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 86 = false ∨ valuation q 97 = false := by
  rw [value86, value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (437 : Vertex) (421 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 216 = true ∨ valuation q 97 = true ∨ valuation q 102 = true := by
  rw [value96, value97, value102, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(439 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (421 : Vertex) [(439 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 216 = true ∨ valuation q 86 = true ∨ valuation q 102 = true := by
  rw [value86, value96, value102, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(421 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (439 : Vertex) [(421 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 49 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value49, value88, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (183 : Vertex) (423 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 49 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value49, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (183 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 217 = true ∨ valuation q 49 = true ∨ valuation q 95 = true ∨ valuation q 96 = true := by
  rw [value49, value95, value96, value97, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(183 : Vertex), (435 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (423 : Vertex) [(183 : Vertex), (435 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 217 = true ∨ valuation q 49 = true ∨ valuation q 88 = true ∨ valuation q 96 = true := by
  rw [value49, value88, value96, value97, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(183 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (435 : Vertex) [(183 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E004.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112004
