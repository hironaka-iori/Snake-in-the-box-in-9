import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 82 = false := by
  rw [value29, value30, value32, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (122 : Vertex) (124 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 71 = false ∨ valuation q 82 = false := by
  rw [value29, value30, value71, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (122 : Vertex) (248 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 71 = false ∨ valuation q 82 = false := by
  rw [value29, value32, value71, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (124 : Vertex) (248 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value13, value21, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (120 : Vertex) (56 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 21 = false ∨ valuation q 30 = false := by
  rw [value21, value30, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (120 : Vertex) (104 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 25 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value25, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (122 : Vertex) (114 : Vertex) (120 : Vertex) (123 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 150 = true ∨ valuation q 29 = true ∨ valuation q 31 = true := by
  rw [value29, value30, value31, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(120 : Vertex), (123 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (114 : Vertex) [(120 : Vertex), (123 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 150 = true ∨ valuation q 25 = true ∨ valuation q 31 = true := by
  rw [value25, value30, value31, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(114 : Vertex), (123 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (120 : Vertex) [(114 : Vertex), (123 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 150 = true ∨ valuation q 25 = true ∨ valuation q 29 = true := by
  rw [value25, value29, value30, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(114 : Vertex), (120 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (123 : Vertex) [(114 : Vertex), (120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 31 = true := by
  rw [value31, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (123 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 83 = false := by
  rw [value26, value30, value31, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (123 : Vertex) (115 : Vertex) (122 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 26 = false ∨ valuation q 83 = false := by
  rw [value26, value83, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (123 : Vertex) (115 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 30 = false ∨ valuation q 83 = false := by
  rw [value30, value83, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (123 : Vertex) (122 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 151 = true ∨ valuation q 26 = true ∨ valuation q 83 = true := by
  rw [value26, value31, value83, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (123 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(115 : Vertex), (379 : Vertex)] := by decide
  have hg := other_cover q (123 : Vertex) (122 : Vertex) [(115 : Vertex), (379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 151 = true ∨ valuation q 26 = true ∨ valuation q 30 = true := by
  rw [value26, value30, value31, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (123 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(115 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (123 : Vertex) (379 : Vertex) [(115 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 33 = false := by
  rw [value27, value29, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (124 : Vertex) (116 : Vertex) (120 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 152 = true ∨ valuation q 29 = true ∨ valuation q 33 = true := by
  rw [value29, value32, value33, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(120 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (116 : Vertex) [(120 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 152 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value27, value29, value32, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(116 : Vertex), (120 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (125 : Vertex) [(116 : Vertex), (120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 33 = true := by
  rw [value33, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (125 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value22, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ∈ [(109 : Vertex), (124 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (125 : Vertex) [(109 : Vertex), (124 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 22 = false ∨ valuation q 32 = false := by
  rw [value22, value32, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (125 : Vertex) (109 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 153 = true ∨ valuation q 32 = true := by
  rw [value32, value33, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(124 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (109 : Vertex) [(124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 153 = true ∨ valuation q 22 = true := by
  rw [value22, value33, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (124 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 34 = true := by
  rw [value34, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (160 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 44 = false := by
  rw [value34, value35, value36, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 84 = false := by
  rw [value34, value35, value36, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 84 = false := by
  rw [value34, value35, value44, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 44 = false ∨ valuation q 84 = false := by
  rw [value34, value36, value44, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 35 = false ∨ valuation q 84 = false := by
  rw [value35, value84, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (160 : Vertex) (161 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 36 = false ∨ valuation q 84 = false := by
  rw [value36, value84, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (160 : Vertex) (162 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 44 = false ∨ valuation q 84 = false := by
  rw [value44, value84, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (160 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 39 = true := by
  rw [value34, value35, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ∈ [(160 : Vertex), (163 : Vertex), (169 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (161 : Vertex) [(160 : Vertex), (163 : Vertex), (169 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E004.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112004
