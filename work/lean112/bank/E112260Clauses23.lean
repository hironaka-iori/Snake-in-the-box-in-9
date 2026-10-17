import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 239 = true ∨ valuation q 49 = true ∨ valuation q 113 = true := by
  rw [value49, value112, value113, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(210 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (338 : Vertex) [(210 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 113 = true := by
  rw [value113, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (467 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 104 = false ∨ valuation q 112 = false := by
  rw [value104, value112, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (467 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide)

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 240 = true ∨ valuation q 112 = true := by
  rw [value112, value113, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(466 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (451 : Vertex) [(466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 240 = true ∨ valuation q 104 = true := by
  rw [value104, value113, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(451 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (466 : Vertex) [(451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 50 = false ∨ valuation q 105 = false ∨ valuation q 115 = false := by
  rw [value50, value105, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (212 : Vertex) (452 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 241 = true ∨ valuation q 50 = true ∨ valuation q 105 = true := by
  rw [value50, value105, value114, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(212 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (469 : Vertex) [(212 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value106, value114, value115, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(453 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (341 : Vertex) [(453 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 91 = true ∨ valuation q 114 = true := by
  rw [value91, value114, value115, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(341 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (453 : Vertex) [(341 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 91 = true ∨ valuation q 106 = true := by
  rw [value91, value106, value115, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(341 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (468 : Vertex) [(341 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 243 = true ∨ valuation q 56 = true ∨ valuation q 117 = true := by
  rw [value56, value116, value117, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(226 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (490 : Vertex) [(226 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 104 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value104, value116, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (451 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 105 = false ∨ valuation q 119 = false ∨ valuation q 124 = false := by
  rw [value105, value118, value119, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (484 : Vertex) (452 : Vertex) (485 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 119 = true ∨ valuation q 124 = true := by
  rw [value118, value119, value124, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(485 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (452 : Vertex) [(485 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 105 = true ∨ valuation q 124 = true := by
  rw [value105, value118, value124, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(452 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (485 : Vertex) [(452 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 105 = true ∨ valuation q 119 = true := by
  rw [value105, value118, value119, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (484 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(452 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (484 : Vertex) (492 : Vertex) [(452 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 58 = false ∨ valuation q 94 = false ∨ valuation q 120 = false := by
  rw [value58, value94, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (357 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 58 = false ∨ valuation q 94 = false ∨ valuation q 125 = false := by
  rw [value58, value94, value119, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (357 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 118 = false ∨ valuation q 120 = false ∨ valuation q 125 = false := by
  rw [value118, value119, value120, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (484 : Vertex) (487 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 246 = true ∨ valuation q 94 = true ∨ valuation q 106 = true ∨ valuation q 118 = true ∨ valuation q 120 = true ∨ valuation q 125 = true := by
  rw [value94, value106, value118, value119, value120, value125, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(357 : Vertex), (453 : Vertex), (484 : Vertex), (487 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (485 : Vertex) (229 : Vertex) [(357 : Vertex), (453 : Vertex), (484 : Vertex), (487 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 246 = true ∨ valuation q 58 = true ∨ valuation q 94 = true ∨ valuation q 106 = true ∨ valuation q 120 = true ∨ valuation q 125 = true := by
  rw [value58, value94, value106, value119, value120, value125, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (484 : Vertex) → w ∈ [(229 : Vertex), (357 : Vertex), (453 : Vertex), (487 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (485 : Vertex) (484 : Vertex) [(229 : Vertex), (357 : Vertex), (453 : Vertex), (487 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 96 = false ∨ valuation q 117 = false ∨ valuation q 119 = false := by
  rw [value96, value117, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (483 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 96 = false ∨ valuation q 117 = false ∨ valuation q 126 = false := by
  rw [value96, value117, value120, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (483 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 96 = false ∨ valuation q 117 = false ∨ valuation q 127 = false := by
  rw [value96, value117, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (483 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 96 = false ∨ valuation q 119 = false ∨ valuation q 126 = false := by
  rw [value96, value119, value120, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (485 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 96 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value96, value119, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (485 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 96 = false ∨ valuation q 126 = false ∨ valuation q 127 = false := by
  rw [value96, value120, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (495 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 126 = false := by
  rw [value117, value119, value120, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (483 : Vertex) (485 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 127 = false := by
  rw [value117, value119, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (483 : Vertex) (485 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 117 = false ∨ valuation q 126 = false ∨ valuation q 127 = false := by
  rw [value117, value120, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (483 : Vertex) (495 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 119 = false ∨ valuation q 126 = false ∨ valuation q 127 = false := by
  rw [value119, value120, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (485 : Vertex) (495 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 96 = true ∨ valuation q 117 = true ∨ valuation q 126 = true ∨ valuation q 127 = true := by
  rw [value96, value117, value120, value126, value127, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(359 : Vertex), (483 : Vertex), (495 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (485 : Vertex) [(359 : Vertex), (483 : Vertex), (495 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block23 (q : Snake 81) (h : Conditions q) : B112E260.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112260
