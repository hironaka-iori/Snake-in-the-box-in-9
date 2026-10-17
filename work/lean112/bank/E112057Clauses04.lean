import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 82 = false := by
  rw [value13, value19, value33, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (29 : Vertex) (85 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 50 = false ∨ valuation q 82 = false := by
  rw [value13, value19, value50, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (29 : Vertex) (149 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 33 = false ∨ valuation q 50 = false ∨ valuation q 82 = false := by
  rw [value13, value33, value50, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (85 : Vertex) (149 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 4 = false ∨ valuation q 15 = false := by
  rw [value4, value15, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (21 : Vertex) (5 : Vertex) (23 : Vertex) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 51 = false := by
  rw [value11, value14, value15, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (18 : Vertex) (23 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 83 = false := by
  rw [value11, value14, value15, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (18 : Vertex) (23 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 11 = false ∨ valuation q 15 = false := by
  rw [value11, value15, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (22 : Vertex) (18 : Vertex) (23 : Vertex) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 141 = true ∨ valuation q 11 = true ∨ valuation q 51 = true ∨ valuation q 83 = true := by
  rw [value11, value14, value51, value83, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(18 : Vertex), (150 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (23 : Vertex) [(18 : Vertex), (150 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 20 = false := by
  rw [value12, value13, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (21 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 52 = false := by
  rw [value12, value13, value15, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (21 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 84 = false := by
  rw [value12, value13, value15, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (21 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 52 = false ∨ valuation q 84 = false := by
  rw [value12, value15, value52, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (19 : Vertex) (151 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value13, value14, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (21 : Vertex) (22 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 52 = false := by
  rw [value13, value14, value15, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (21 : Vertex) (22 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 52 = false := by
  rw [value13, value15, value20, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (23 : Vertex) (21 : Vertex) (31 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 52 = true ∨ valuation q 84 = true := by
  rw [value13, value14, value15, value20, value52, value84, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(21 : Vertex), (22 : Vertex), (31 : Vertex), (151 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (19 : Vertex) [(21 : Vertex), (22 : Vertex), (31 : Vertex), (151 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 12 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 52 = true ∨ valuation q 84 = true := by
  rw [value12, value14, value15, value20, value52, value84, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(19 : Vertex), (22 : Vertex), (31 : Vertex), (151 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (21 : Vertex) [(19 : Vertex), (22 : Vertex), (31 : Vertex), (151 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 20 = true ∨ valuation q 52 = true ∨ valuation q 84 = true := by
  rw [value12, value13, value15, value20, value52, value84, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(19 : Vertex), (21 : Vertex), (31 : Vertex), (151 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (22 : Vertex) [(19 : Vertex), (21 : Vertex), (31 : Vertex), (151 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 52 = true ∨ valuation q 84 = true := by
  rw [value12, value13, value14, value15, value52, value84, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(19 : Vertex), (21 : Vertex), (22 : Vertex), (151 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (31 : Vertex) [(19 : Vertex), (21 : Vertex), (22 : Vertex), (151 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 84 = true := by
  rw [value12, value13, value14, value15, value20, value84, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(19 : Vertex), (21 : Vertex), (22 : Vertex), (31 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (151 : Vertex) [(19 : Vertex), (21 : Vertex), (22 : Vertex), (31 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 142 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 52 = true := by
  rw [value12, value13, value14, value15, value20, value52, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(19 : Vertex), (21 : Vertex), (22 : Vertex), (31 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (279 : Vertex) [(19 : Vertex), (21 : Vertex), (22 : Vertex), (31 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 10 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value10, value16, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (25 : Vertex) (17 : Vertex) (27 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 10 = false ∨ valuation q 17 = false ∨ valuation q 86 = false := by
  rw [value10, value16, value17, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (25 : Vertex) (17 : Vertex) (27 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 86 = false := by
  rw [value10, value16, value19, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (25 : Vertex) (17 : Vertex) (29 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 86 = false := by
  rw [value16, value17, value19, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (25 : Vertex) (27 : Vertex) (29 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value17, value19, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (25 : Vertex) (27 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 86 = true := by
  rw [value16, value17, value19, value86, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(27 : Vertex), (29 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (17 : Vertex) [(27 : Vertex), (29 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 10 = true ∨ valuation q 19 = true ∨ valuation q 86 = true := by
  rw [value10, value16, value19, value86, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(17 : Vertex), (29 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (27 : Vertex) [(17 : Vertex), (29 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 143 = true ∨ valuation q 10 = true ∨ valuation q 17 = true ∨ valuation q 86 = true := by
  rw [value10, value16, value17, value86, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(17 : Vertex), (27 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (29 : Vertex) [(17 : Vertex), (27 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 88 = false := by
  rw [value12, value16, value17, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (19 : Vertex) (25 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 88 = false := by
  rw [value12, value17, value20, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (27 : Vertex) (19 : Vertex) (31 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 88 = true := by
  rw [value16, value17, value20, value88, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(25 : Vertex), (31 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (19 : Vertex) [(25 : Vertex), (31 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E057.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112057
