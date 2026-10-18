import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 120 = true ∨ valuation q 124 = true := by
  rw [value119, value120, value124, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(503 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (500 : Vertex) [(503 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 118 = true ∨ valuation q 124 = true := by
  rw [value118, value119, value124, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(500 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (503 : Vertex) [(500 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 118 = true ∨ valuation q 120 = true := by
  rw [value118, value119, value120, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(500 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (509 : Vertex) [(500 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 119 = true := by
  rw [value119, value120, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(501 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (487 : Vertex) [(501 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 112 = true := by
  rw [value112, value120, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (501 : Vertex) → w ∈ [(487 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (501 : Vertex) [(487 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 114 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value114, value121, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 114 = true ∨ valuation q 124 = true := by
  rw [value114, value121, value124, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(489 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (507 : Vertex) [(489 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 114 = true ∨ valuation q 123 = true := by
  rw [value114, value121, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(489 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (509 : Vertex) [(489 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 104 = true ∨ valuation q 123 = true := by
  rw [value104, value122, value123, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(442 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (498 : Vertex) [(442 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 104 = true ∨ valuation q 117 = true := by
  rw [value104, value117, value122, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(442 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (507 : Vertex) [(442 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 105 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value105, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (443 : Vertex) (505 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 247 = true ∨ valuation q 105 = true ∨ valuation q 122 = true := by
  rw [value105, value122, value123, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(443 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (505 : Vertex) [(443 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 247 = true ∨ valuation q 105 = true ∨ valuation q 121 = true := by
  rw [value105, value121, value123, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(443 : Vertex), (505 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (506 : Vertex) [(443 : Vertex), (505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (35 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 129 = false := by
  rw [value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (41 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 130 = false := by
  rw [value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (42 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (47 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 134 = false := by
  rw [value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (49 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 136 = false := by
  rw [value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (52 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 138 = false := by
  rw [value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (56 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 141 = false := by
  rw [value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (62 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (98 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 144 = false := by
  rw [value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (103 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 145 = false := by
  rw [value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (104 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 148 = false := by
  rw [value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (110 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 149 = false := by
  rw [value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (117 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 152 = false := by
  rw [value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (121 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 153 = false := by
  rw [value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (122 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 157 = false := by
  rw [value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (161 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 158 = false := by
  rw [value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (162 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 159 = false := by
  rw [value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (164 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 162 = false := by
  rw [value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (168 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block23 (q : Snake 81) (h : Conditions q) : B112E008.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112008
