import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 140 = true ∨ valuation q 17 = true ∨ valuation q 20 = true := by
  rw [value17, value20, value23, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(132 : Vertex), (136 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (142 : Vertex) [(132 : Vertex), (136 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true ∨ valuation q 18 = true ∨ valuation q 23 = true := by
  rw [value18, value23, value24, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(134 : Vertex), (140 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (138 : Vertex) [(134 : Vertex), (140 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true ∨ valuation q 18 = true ∨ valuation q 22 = true := by
  rw [value18, value22, value24, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(134 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (140 : Vertex) [(134 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 142 = true ∨ valuation q 17 = true := by
  rw [value17, value25, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(132 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (149 : Vertex) [(132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 143 = true ∨ valuation q 27 = true ∨ valuation q 31 = true := by
  rw [value26, value27, value31, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(151 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (148 : Vertex) [(151 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 143 = true ∨ valuation q 25 = true ∨ valuation q 31 = true := by
  rw [value25, value26, value31, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(148 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (151 : Vertex) [(148 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 143 = true ∨ valuation q 25 = true ∨ valuation q 27 = true := by
  rw [value25, value26, value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(148 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (157 : Vertex) [(148 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 19 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value19, value26, value27, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (135 : Vertex) (149 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 144 = true ∨ valuation q 26 = true ∨ valuation q 32 = true := by
  rw [value26, value27, value32, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(149 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (135 : Vertex) [(149 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 144 = true ∨ valuation q 19 = true ∨ valuation q 32 = true := by
  rw [value19, value27, value32, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(135 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (149 : Vertex) [(135 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 144 = true ∨ valuation q 19 = true ∨ valuation q 26 = true := by
  rw [value19, value26, value27, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(135 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (159 : Vertex) [(135 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 145 = true ∨ valuation q 30 = true ∨ valuation q 31 = true := by
  rw [value28, value30, value31, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(155 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (137 : Vertex) [(155 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 145 = true ∨ valuation q 21 = true ∨ valuation q 31 = true := by
  rw [value21, value28, value31, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(137 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (155 : Vertex) [(137 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 32 = false := by
  rw [value28, value29, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (153 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 147 = true ∨ valuation q 29 = true ∨ valuation q 32 = true := by
  rw [value29, value30, value32, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (153 : Vertex) [(154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 13 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value13, value26, value28, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (29 : Vertex) (149 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 13 = false ∨ valuation q 26 = false ∨ valuation q 40 = false := by
  rw [value13, value26, value31, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (29 : Vertex) (149 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 13 = false ∨ valuation q 26 = false ∨ valuation q 102 = false := by
  rw [value13, value26, value31, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (29 : Vertex) (149 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 13 = false ∨ valuation q 28 = false ∨ valuation q 102 = false := by
  rw [value13, value28, value31, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (29 : Vertex) (153 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 13 = false ∨ valuation q 32 = false ∨ valuation q 40 = false := by
  rw [value13, value31, value32, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (29 : Vertex) (159 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 13 = false ∨ valuation q 32 = false ∨ valuation q 102 = false := by
  rw [value13, value31, value32, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (29 : Vertex) (159 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 13 = false ∨ valuation q 40 = false ∨ valuation q 102 = false := by
  rw [value13, value31, value40, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (29 : Vertex) (221 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 32 = false := by
  rw [value26, value28, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (153 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 40 = false := by
  rw [value26, value28, value31, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (153 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 102 = false := by
  rw [value26, value28, value31, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (153 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 26 = false ∨ valuation q 32 = false ∨ valuation q 40 = false := by
  rw [value26, value31, value32, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (159 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 28 = false ∨ valuation q 32 = false ∨ valuation q 40 = false := by
  rw [value28, value31, value32, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (153 : Vertex) (159 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 40 = false ∨ valuation q 102 = false := by
  rw [value31, value32, value40, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (159 : Vertex) (221 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 149 = true ∨ valuation q 27 = true ∨ valuation q 31 = true := by
  rw [value27, value31, value32, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(151 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (155 : Vertex) [(151 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 18 = false ∨ valuation q 37 = false ∨ valuation q 43 = false := by
  rw [value18, value33, value37, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (214 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 150 = true ∨ valuation q 18 = true ∨ valuation q 37 = true := by
  rw [value18, value33, value37, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(134 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (230 : Vertex) [(134 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 151 = true ∨ valuation q 35 = true := by
  rw [value34, value35, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(205 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (137 : Vertex) [(205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E203.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112203
