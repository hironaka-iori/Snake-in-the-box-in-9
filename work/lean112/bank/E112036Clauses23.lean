import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 248 = true ∨ valuation q 101 = true ∨ valuation q 112 = true := by
  rw [value101, value112, value120, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(433 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (499 : Vertex) [(433 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 122 = false ∨ valuation q 124 = false ∨ valuation q 125 = false := by
  rw [value121, value122, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (499 : Vertex) (502 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 249 = true ∨ valuation q 124 = true ∨ valuation q 125 = true := by
  rw [value121, value124, value125, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(502 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (499 : Vertex) [(502 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 102 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value102, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (497 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 120 = true ∨ valuation q 121 = true := by
  rw [value120, value121, value122, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(497 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (435 : Vertex) [(497 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 102 = true ∨ valuation q 121 = true := by
  rw [value102, value121, value122, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(435 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (497 : Vertex) [(435 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 250 = true ∨ valuation q 102 = true ∨ valuation q 120 = true := by
  rw [value102, value120, value122, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(435 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (498 : Vertex) [(435 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 61 = false ∨ valuation q 103 = false ∨ valuation q 124 = false := by
  rw [value61, value103, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (436 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 61 = false ∨ valuation q 103 = false ∨ valuation q 126 = false := by
  rw [value61, value103, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (436 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 61 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value61, value123, value124, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 103 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value103, value123, value124, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (436 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 251 = true ∨ valuation q 61 = true ∨ valuation q 103 = true ∨ valuation q 124 = true := by
  rw [value61, value103, value123, value124, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (500 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(244 : Vertex), (436 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (500 : Vertex) (508 : Vertex) [(244 : Vertex), (436 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 113 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value113, value121, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (486 : Vertex) (498 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 113 = false ∨ valuation q 121 = false ∨ valuation q 128 = false := by
  rw [value113, value121, value124, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (486 : Vertex) (498 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 252 = true ∨ valuation q 113 = true ∨ valuation q 121 = true ∨ valuation q 128 = true := by
  rw [value113, value121, value124, value128, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(486 : Vertex), (498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (500 : Vertex) [(486 : Vertex), (498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 252 = true ∨ valuation q 113 = true ∨ valuation q 121 = true ∨ valuation q 123 = true := by
  rw [value113, value121, value123, value124, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(486 : Vertex), (498 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (510 : Vertex) [(486 : Vertex), (498 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 66 = false ∨ valuation q 108 = false ∨ valuation q 121 = false := by
  rw [value66, value108, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (250 : Vertex) (442 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 66 = false ∨ valuation q 121 = false ∨ valuation q 128 = false := by
  rw [value66, value121, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (250 : Vertex) (498 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 108 = true ∨ valuation q 121 = true ∨ valuation q 128 = true := by
  rw [value108, value121, value125, value128, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(442 : Vertex), (498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (250 : Vertex) [(442 : Vertex), (498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 66 = true ∨ valuation q 121 = true ∨ valuation q 128 = true := by
  rw [value66, value121, value125, value128, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(250 : Vertex), (498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (442 : Vertex) [(250 : Vertex), (498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 66 = true ∨ valuation q 108 = true ∨ valuation q 128 = true := by
  rw [value66, value108, value125, value128, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(250 : Vertex), (442 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (498 : Vertex) [(250 : Vertex), (442 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 66 = true ∨ valuation q 108 = true ∨ valuation q 121 = true := by
  rw [value66, value108, value121, value125, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(250 : Vertex), (442 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (510 : Vertex) [(250 : Vertex), (442 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 123 = false ∨ valuation q 127 = false ∨ valuation q 128 = false := by
  rw [value123, value126, value127, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (500 : Vertex) (509 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 254 = true ∨ valuation q 127 = true ∨ valuation q 128 = true := by
  rw [value126, value127, value128, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(509 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (500 : Vertex) [(509 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 254 = true ∨ valuation q 123 = true ∨ valuation q 128 = true := by
  rw [value123, value126, value128, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(500 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (509 : Vertex) [(500 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 254 = true ∨ valuation q 123 = true ∨ valuation q 127 = true := by
  rw [value123, value126, value127, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(500 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (510 : Vertex) [(500 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 127 = true := by
  rw [value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (509 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 118 = true ∨ valuation q 126 = true := by
  rw [value118, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ∈ [(493 : Vertex), (508 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (509 : Vertex) [(493 : Vertex), (508 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value118, value126, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (509 : Vertex) (493 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide)

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 118 = true := by
  rw [value118, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(493 : Vertex)] := by decide
  have hg := other_cover q (509 : Vertex) (508 : Vertex) [(493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 124 = false ∨ valuation q 125 = false ∨ valuation q 126 = false := by
  rw [value124, value125, value126, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (510 : Vertex) (502 : Vertex) (506 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 130 = false := by
  rw [value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (35 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block23 (q : Snake 81) (h : Conditions q) : B112E036.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112036
