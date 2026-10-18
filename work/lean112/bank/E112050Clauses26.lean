import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 121 = false ∨ valuation q 124 = false ∨ valuation q 128 = false := by
  rw [value121, value124, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (466 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 124 = false ∨ valuation q 127 = false ∨ valuation q 128 = false := by
  rw [value124, value126, value127, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (472 : Vertex) (477 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 254 = true ∨ valuation q 124 = true ∨ valuation q 128 = true := by
  rw [value124, value126, value128, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(472 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (477 : Vertex) [(472 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 254 = true ∨ valuation q 124 = true ∨ valuation q 127 = true := by
  rw [value124, value126, value127, value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(472 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (478 : Vertex) [(472 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 106 = true ∨ valuation q 117 = true ∨ valuation q 126 = true := by
  rw [value106, value117, value126, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(413 : Vertex), (461 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (221 : Vertex) [(413 : Vertex), (461 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 48 = true ∨ valuation q 117 = true ∨ valuation q 126 = true := by
  rw [value48, value117, value126, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(221 : Vertex), (461 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (413 : Vertex) [(221 : Vertex), (461 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 48 = true ∨ valuation q 106 = true ∨ valuation q 117 = true := by
  rw [value48, value106, value117, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(221 : Vertex), (413 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (476 : Vertex) [(221 : Vertex), (413 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 107 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value107, value118, value126, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (414 : Vertex) (462 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 118 = false ∨ valuation q 125 = false ∨ valuation q 126 = false := by
  rw [value118, value125, value126, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (462 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 256 = true ∨ valuation q 118 = true ∨ valuation q 125 = true ∨ valuation q 126 = true := by
  rw [value118, value125, value126, value128, value256]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(462 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (414 : Vertex) [(462 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 256 = true ∨ valuation q 107 = true ∨ valuation q 125 = true ∨ valuation q 126 = true := by
  rw [value107, value125, value126, value128, value256]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(414 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (462 : Vertex) [(414 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 256 = true ∨ valuation q 107 = true ∨ valuation q 118 = true ∨ valuation q 126 = true := by
  rw [value107, value118, value126, value128, value256]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(414 : Vertex), (462 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (474 : Vertex) [(414 : Vertex), (462 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 256 = true ∨ valuation q 107 = true ∨ valuation q 118 = true ∨ valuation q 125 = true := by
  rw [value107, value118, value125, value128, value256]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(414 : Vertex), (462 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (476 : Vertex) [(414 : Vertex), (462 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 131 = false := by
  rw [value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (76 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 133 = false := by
  rw [value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (82 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 136 = false := by
  rw [value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (88 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 138 = false := by
  rw [value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (93 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 139 = false := by
  rw [value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (94 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 140 = false := by
  rw [value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (103 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 141 = false := by
  rw [value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (118 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 144 = false := by
  rw [value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (131 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 146 = false := by
  rw [value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (133 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 147 = false := by
  rw [value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (137 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 153 = false := by
  rw [value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (146 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 155 = false := by
  rw [value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (151 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 156 = false := by
  rw [value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (152 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 158 = false := by
  rw [value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (158 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 163 = false := by
  rw [value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (199 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 164 = false := by
  rw [value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (200 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 167 = false := by
  rw [value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (206 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 170 = false := by
  rw [value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (213 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 171 = false := by
  rw [value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (214 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block26 (q : Snake 81) (h : Conditions q) : B112E050.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112050
