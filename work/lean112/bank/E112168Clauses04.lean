import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 146 = true ∨ valuation q 26 = true ∨ valuation q 30 = true ∨ valuation q 52 = true := by
  rw [value26, value30, value32, value52, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(134 : Vertex), (138 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (140 : Vertex) [(134 : Vertex), (138 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 147 = true ∨ valuation q 54 = true := by
  rw [value33, value54, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(208 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (148 : Vertex) [(208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 147 = true ∨ valuation q 34 = true := by
  rw [value33, value34, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(148 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (208 : Vertex) [(148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 148 = true ∨ valuation q 33 = true ∨ valuation q 35 = true := by
  rw [value33, value34, value35, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(144 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (132 : Vertex) [(144 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 148 = true ∨ valuation q 25 = true ∨ valuation q 35 = true := by
  rw [value25, value34, value35, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(132 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(132 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 148 = true ∨ valuation q 25 = true ∨ valuation q 33 = true := by
  rw [value25, value33, value34, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(132 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (149 : Vertex) [(132 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value34, value35, value36, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (148 : Vertex) (151 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 27 = false ∨ valuation q 35 = false ∨ valuation q 41 = false := by
  rw [value27, value35, value36, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (135 : Vertex) (149 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 150 = true ∨ valuation q 35 = true ∨ valuation q 41 = true := by
  rw [value35, value36, value41, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(149 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (135 : Vertex) [(149 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 150 = true ∨ valuation q 27 = true ∨ valuation q 41 = true := by
  rw [value27, value36, value41, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(135 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (149 : Vertex) [(135 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 150 = true ∨ valuation q 27 = true ∨ valuation q 35 = true := by
  rw [value27, value35, value36, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(135 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (159 : Vertex) [(135 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 29 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value29, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (155 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 29 = false ∨ valuation q 39 = false ∨ valuation q 60 = false := by
  rw [value29, value37, value39, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (155 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 60 = false := by
  rw [value37, value39, value40, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (155 : Vertex) (157 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 151 = true ∨ valuation q 29 = true ∨ valuation q 40 = true ∨ valuation q 60 = true := by
  rw [value29, value37, value40, value60, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(137 : Vertex), (157 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (155 : Vertex) [(137 : Vertex), (157 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 30 = false ∨ valuation q 39 = false ∨ valuation q 61 = false := by
  rw [value30, value38, value39, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 30 = false ∨ valuation q 39 = false ∨ valuation q 93 = false := by
  rw [value30, value38, value39, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 61 = false ∨ valuation q 93 = false := by
  rw [value38, value39, value61, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (155 : Vertex) (218 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 153 = true ∨ valuation q 38 = true ∨ valuation q 41 = true := by
  rw [value38, value39, value41, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (153 : Vertex) [(154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 153 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value37, value39, value41, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(153 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (154 : Vertex) [(153 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 153 = true ∨ valuation q 37 = true ∨ valuation q 38 = true := by
  rw [value37, value38, value39, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(153 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (159 : Vertex) [(153 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 63 = false := by
  rw [value35, value37, value40, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (153 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 95 = false := by
  rw [value35, value37, value40, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (153 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 63 = false := by
  rw [value35, value40, value41, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (159 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 37 = false ∨ valuation q 63 = false ∨ valuation q 95 = false := by
  rw [value37, value40, value63, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (153 : Vertex) (221 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value36, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (151 : Vertex) (155 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 54 = false := by
  rw [value42, value43, value44, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (194 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 156 = true ∨ valuation q 44 = true ∨ valuation q 54 = true := by
  rw [value42, value44, value54, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(194 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 157 = true ∨ valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 55 = true := by
  rw [value42, value43, value45, value48, value55, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(192 : Vertex), (195 : Vertex), (201 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (197 : Vertex) [(192 : Vertex), (195 : Vertex), (201 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 157 = true ∨ valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 48 = true := by
  rw [value42, value43, value45, value46, value48, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(192 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (209 : Vertex) [(192 : Vertex), (195 : Vertex), (197 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 45 = false := by
  rw [value7, value23, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 56 = false := by
  rw [value7, value23, value44, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (66 : Vertex) (130 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E168.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112168
