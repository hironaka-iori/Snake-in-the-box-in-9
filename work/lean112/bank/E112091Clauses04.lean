import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 147 = true ∨ valuation q 39 = true ∨ valuation q 59 = true ∨ valuation q 82 = true := by
  rw [value39, value41, value59, value82, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(170 : Vertex), (238 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (166 : Vertex) [(170 : Vertex), (238 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 147 = true ∨ valuation q 36 = true ∨ valuation q 59 = true ∨ valuation q 82 = true := by
  rw [value36, value41, value59, value82, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(166 : Vertex), (238 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (170 : Vertex) [(166 : Vertex), (238 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 46 = false ∨ valuation q 50 = false ∨ valuation q 86 = false := by
  rw [value42, value46, value50, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (183 : Vertex) (187 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 148 = true ∨ valuation q 50 = true ∨ valuation q 86 = true := by
  rw [value42, value50, value86, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(187 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (183 : Vertex) [(187 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 148 = true ∨ valuation q 46 = true ∨ valuation q 50 = true := by
  rw [value42, value46, value50, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(183 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (435 : Vertex) [(183 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value35, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (164 : Vertex) (181 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 62 = false := by
  rw [value35, value43, value44, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (164 : Vertex) (181 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 87 = false := by
  rw [value35, value43, value44, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (164 : Vertex) (181 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 45 = false ∨ valuation q 62 = false := by
  rw [value35, value43, value45, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (164 : Vertex) (182 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 45 = false ∨ valuation q 87 = false := by
  rw [value35, value43, value45, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (164 : Vertex) (182 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 62 = false ∨ valuation q 87 = false := by
  rw [value35, value43, value62, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (164 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 62 = false := by
  rw [value43, value44, value45, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (181 : Vertex) (182 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 87 = false := by
  rw [value43, value44, value45, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (181 : Vertex) (182 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 62 = false ∨ valuation q 87 = false := by
  rw [value43, value45, value62, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (182 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value43, value44, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (180 : Vertex) (183 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 150 = true ∨ valuation q 46 = true ∨ valuation q 51 = true := by
  rw [value44, value46, value51, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(183 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (180 : Vertex) [(183 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 150 = true ∨ valuation q 43 = true ∨ valuation q 51 = true := by
  rw [value43, value44, value51, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(180 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (183 : Vertex) [(180 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 150 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value44, value46, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(180 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (189 : Vertex) [(180 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 151 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value45, value46, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(180 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (166 : Vertex) [(180 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 151 = true ∨ valuation q 36 = true ∨ valuation q 46 = true := by
  rw [value36, value45, value46, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(166 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (180 : Vertex) [(166 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 151 = true ∨ valuation q 36 = true ∨ valuation q 43 = true := by
  rw [value36, value43, value45, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(166 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (183 : Vertex) [(166 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 42 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value42, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (179 : Vertex) (181 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 152 = true ∨ valuation q 44 = true ∨ valuation q 45 = true := by
  rw [value44, value45, value46, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(181 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (179 : Vertex) [(181 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 37 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value37, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (185 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 153 = true ∨ valuation q 37 = true ∨ valuation q 49 = true := by
  rw [value37, value47, value49, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(168 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (185 : Vertex) [(168 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 153 = true ∨ valuation q 37 = true ∨ valuation q 48 = true := by
  rw [value37, value47, value48, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(168 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (186 : Vertex) [(168 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 38 = true ∨ valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 51 = true := by
  rw [value38, value47, value48, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ∈ [(169 : Vertex), (184 : Vertex), (187 : Vertex), (189 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (185 : Vertex) [(169 : Vertex), (184 : Vertex), (187 : Vertex), (189 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 38 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value38, value47, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (184 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 38 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value38, value48, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (187 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 154 = true ∨ valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 51 = true := by
  rw [value47, value48, value50, value51, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(184 : Vertex), (187 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (169 : Vertex) [(184 : Vertex), (187 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 154 = true ∨ valuation q 38 = true ∨ valuation q 50 = true ∨ valuation q 51 = true := by
  rw [value38, value48, value50, value51, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(169 : Vertex), (187 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (184 : Vertex) [(169 : Vertex), (187 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 154 = true ∨ valuation q 38 = true ∨ valuation q 47 = true ∨ valuation q 50 = true := by
  rw [value38, value47, value48, value50, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(169 : Vertex), (184 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (189 : Vertex) [(169 : Vertex), (184 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E091.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112091
