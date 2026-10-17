import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 240 = true ∨ valuation q 107 = true ∨ valuation q 115 = true ∨ valuation q 120 = true := by
  rw [value107, value115, value119, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(460 : Vertex), (468 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (472 : Vertex) [(460 : Vertex), (468 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 240 = true ∨ valuation q 107 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value107, value115, value116, value119, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(460 : Vertex), (468 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (478 : Vertex) [(460 : Vertex), (468 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 120 = true := by
  rw [value120, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (478 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 109 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 121 = true := by
  rw [value109, value117, value119, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ∈ [(462 : Vertex), (474 : Vertex), (476 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (478 : Vertex) [(462 : Vertex), (474 : Vertex), (476 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 109 = false ∨ valuation q 117 = false ∨ valuation q 121 = false := by
  rw [value109, value117, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (462 : Vertex) (474 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value109, value119, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (478 : Vertex) (462 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide)

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 241 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 121 = true := by
  rw [value117, value119, value120, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(474 : Vertex), (476 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (462 : Vertex) [(474 : Vertex), (476 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 241 = true ∨ valuation q 109 = true ∨ valuation q 119 = true ∨ valuation q 121 = true := by
  rw [value109, value119, value120, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(462 : Vertex), (476 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (474 : Vertex) [(462 : Vertex), (476 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 241 = true ∨ valuation q 109 = true ∨ valuation q 117 = true ∨ valuation q 121 = true := by
  rw [value109, value117, value120, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(462 : Vertex), (474 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (476 : Vertex) [(462 : Vertex), (474 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 241 = true ∨ valuation q 109 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value109, value117, value119, value120, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(462 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (479 : Vertex) [(462 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 98 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value98, value110, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (415 : Vertex) (463 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 98 = false ∨ valuation q 110 = false ∨ valuation q 120 = false := by
  rw [value98, value110, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (415 : Vertex) (463 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 98 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value98, value118, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (415 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value110, value118, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (463 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 242 = true ∨ valuation q 110 = true ∨ valuation q 118 = true ∨ valuation q 120 = true := by
  rw [value110, value118, value120, value121, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (479 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(463 : Vertex), (475 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (479 : Vertex) (415 : Vertex) [(463 : Vertex), (475 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 242 = true ∨ valuation q 98 = true ∨ valuation q 118 = true ∨ valuation q 120 = true := by
  rw [value98, value118, value120, value121, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (479 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(415 : Vertex), (475 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (479 : Vertex) (463 : Vertex) [(415 : Vertex), (475 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 242 = true ∨ valuation q 98 = true ∨ valuation q 110 = true ∨ valuation q 118 = true := by
  rw [value98, value110, value118, value121, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (479 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(415 : Vertex), (463 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (479 : Vertex) (478 : Vertex) [(415 : Vertex), (463 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 122 = false := by
  rw [value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (0 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 124 = false := by
  rw [value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (10 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 125 = false := by
  rw [value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (12 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (66 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 129 = false := by
  rw [value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (68 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 131 = false := by
  rw [value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (71 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 133 = false := by
  rw [value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (75 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 134 = false := by
  rw [value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (77 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 136 = false := by
  rw [value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (80 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 138 = false := by
  rw [value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (83 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 141 = false := by
  rw [value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (92 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (95 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 144 = false := by
  rw [value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (130 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 146 = false := by
  rw [value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (132 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 148 = false := by
  rw [value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (135 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block26 (q : Snake 81) (h : Conditions q) : B112E019.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112019
