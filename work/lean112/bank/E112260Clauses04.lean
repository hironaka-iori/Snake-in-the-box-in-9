import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 12 = true ∨ valuation q 51 = true := by
  rw [value12, value14, value51, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(83 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (71 : Vertex) [(83 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 5 = true ∨ valuation q 51 = true := by
  rw [value5, value14, value51, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(71 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (83 : Vertex) [(71 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 5 = true ∨ valuation q 12 = true := by
  rw [value5, value12, value14, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(71 : Vertex), (83 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (215 : Vertex) [(71 : Vertex), (83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 15 = true := by
  rw [value15, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (89 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 11 = true ∨ valuation q 17 = true ∨ valuation q 52 = true := by
  rw [value11, value15, value17, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ∈ [(81 : Vertex), (93 : Vertex), (217 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (89 : Vertex) [(81 : Vertex), (93 : Vertex), (217 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 11 = false ∨ valuation q 17 = false ∨ valuation q 52 = false := by
  rw [value11, value15, value17, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (81 : Vertex) (93 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 11 = false ∨ valuation q 17 = false := by
  rw [value11, value17, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (89 : Vertex) (81 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 17 = false ∨ valuation q 52 = false := by
  rw [value17, value52, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (89 : Vertex) (93 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 17 = true ∨ valuation q 52 = true := by
  rw [value15, value17, value52, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(93 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (81 : Vertex) [(93 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 11 = true ∨ valuation q 52 = true := by
  rw [value11, value15, value52, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(81 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (93 : Vertex) [(81 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 11 = true ∨ valuation q 17 = true := by
  rw [value11, value15, value17, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(81 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (217 : Vertex) [(81 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 16 = true := by
  rw [value16, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (90 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = true ∨ valuation q 33 = true ∨ valuation q 53 = true := by
  rw [value16, value18, value33, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ∈ [(94 : Vertex), (122 : Vertex), (218 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (90 : Vertex) [(94 : Vertex), (122 : Vertex), (218 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 33 = false ∨ valuation q 53 = false := by
  rw [value33, value53, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (90 : Vertex) (122 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 18 = true ∨ valuation q 53 = true := by
  rw [value16, value18, value53, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(94 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (122 : Vertex) [(94 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 18 = true ∨ valuation q 33 = true := by
  rw [value16, value18, value33, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(94 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (218 : Vertex) [(94 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 34 = true := by
  rw [value17, value34, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (89 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 15 = true := by
  rw [value15, value17, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(89 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (125 : Vertex) [(89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true := by
  rw [value18, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (94 : Vertex) (90 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 2 = false ∨ valuation q 21 = false ∨ valuation q 56 = false := by
  rw [value2, value19, value21, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (98 : Vertex) (66 : Vertex) (102 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 21 = true ∨ valuation q 56 = true := by
  rw [value19, value21, value56, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(102 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (66 : Vertex) [(102 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 2 = true ∨ valuation q 21 = true := by
  rw [value2, value19, value21, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(66 : Vertex), (102 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (226 : Vertex) [(66 : Vertex), (102 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 3 = false ∨ valuation q 22 = false ∨ valuation q 58 = false := by
  rw [value3, value20, value22, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (101 : Vertex) (69 : Vertex) (103 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 147 = true ∨ valuation q 3 = true ∨ valuation q 22 = true ∨ valuation q 94 = true := by
  rw [value3, value20, value22, value94, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(69 : Vertex), (103 : Vertex), (357 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (229 : Vertex) [(69 : Vertex), (103 : Vertex), (357 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 147 = true ∨ valuation q 3 = true ∨ valuation q 22 = true ∨ valuation q 58 = true := by
  rw [value3, value20, value22, value58, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(69 : Vertex), (103 : Vertex), (229 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (357 : Vertex) [(69 : Vertex), (103 : Vertex), (229 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 19 = false ∨ valuation q 27 = false := by
  rw [value4, value19, value21, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (70 : Vertex) (98 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 19 = false ∨ valuation q 31 = false := by
  rw [value4, value19, value21, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (70 : Vertex) (98 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 27 = false := by
  rw [value4, value21, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (70 : Vertex) (103 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 31 = false := by
  rw [value4, value21, value22, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (70 : Vertex) (103 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 27 = false ∨ valuation q 31 = false := by
  rw [value4, value21, value27, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (70 : Vertex) (110 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 27 = false ∨ valuation q 59 = false := by
  rw [value4, value21, value27, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (70 : Vertex) (110 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 4 = false ∨ valuation q 31 = false ∨ valuation q 59 = false := by
  rw [value4, value21, value31, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (70 : Vertex) (118 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E260.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112260
