import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 233 = true ∨ valuation q 94 = true ∨ valuation q 104 = true ∨ valuation q 110 = true := by
  rw [value94, value104, value105, value110, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(423 : Vertex), (437 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (435 : Vertex) [(423 : Vertex), (437 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 233 = true ∨ valuation q 94 = true ∨ valuation q 102 = true ∨ valuation q 110 = true := by
  rw [value94, value102, value105, value110, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (437 : Vertex) [(423 : Vertex), (435 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 233 = true ∨ valuation q 94 = true ∨ valuation q 102 = true ∨ valuation q 104 = true := by
  rw [value94, value102, value104, value105, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (447 : Vertex) [(423 : Vertex), (435 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 95 = false ∨ valuation q 107 = false := by
  rw [value46, value95, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (424 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 95 = false ∨ valuation q 108 = false := by
  rw [value46, value95, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (424 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 46 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value46, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 95 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value95, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 234 = true ∨ valuation q 95 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value95, value106, value107, value108, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(424 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (184 : Vertex) [(424 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 234 = true ∨ valuation q 46 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value46, value106, value107, value108, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(184 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(184 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 234 = true ∨ valuation q 46 = true ∨ valuation q 95 = true ∨ valuation q 108 = true := by
  rw [value46, value95, value106, value108, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (441 : Vertex) [(184 : Vertex), (424 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 234 = true ∨ valuation q 46 = true ∨ valuation q 95 = true ∨ valuation q 107 = true := by
  rw [value46, value95, value106, value107, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(184 : Vertex), (424 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 101 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value101, value106, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (433 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 235 = true ∨ valuation q 101 = true ∨ valuation q 109 = true := by
  rw [value101, value107, value109, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(433 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (440 : Vertex) [(433 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 235 = true ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value101, value106, value107, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(433 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (443 : Vertex) [(433 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 83 = false ∨ valuation q 96 = false ∨ valuation q 106 = false := by
  rw [value83, value96, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (426 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 83 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value83, value96, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 83 = false ∨ valuation q 96 = false ∨ valuation q 125 = false := by
  rw [value83, value96, value108, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (426 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 83 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value83, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 83 = false ∨ valuation q 106 = false ∨ valuation q 125 = false := by
  rw [value83, value106, value108, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 83 = false ∨ valuation q 109 = false ∨ valuation q 125 = false := by
  rw [value83, value108, value109, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value96, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 125 = false := by
  rw [value96, value106, value108, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 125 = false := by
  rw [value96, value108, value109, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 125 = false := by
  rw [value106, value108, value109, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 236 = true ∨ valuation q 96 = true ∨ valuation q 106 = true ∨ valuation q 109 = true ∨ valuation q 125 = true := by
  rw [value96, value106, value108, value109, value125, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(426 : Vertex), (440 : Vertex), (443 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (314 : Vertex) [(426 : Vertex), (440 : Vertex), (443 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 97 = false ∨ valuation q 102 = false ∨ valuation q 107 = false := by
  rw [value97, value102, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 97 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value97, value102, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 97 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value97, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value97, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (442 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 102 = true ∨ valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 110 = true := by
  rw [value102, value107, value108, value109, value110, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(435 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (427 : Vertex) [(435 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 97 = true ∨ valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 110 = true := by
  rw [value97, value107, value108, value109, value110, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(427 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (435 : Vertex) [(427 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 237 = true ∨ valuation q 97 = true ∨ valuation q 102 = true ∨ valuation q 108 = true ∨ valuation q 110 = true := by
  rw [value97, value102, value108, value109, value110, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (441 : Vertex) [(427 : Vertex), (435 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block20 (q : Snake 81) (h : Conditions q) : B112E036.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112036
