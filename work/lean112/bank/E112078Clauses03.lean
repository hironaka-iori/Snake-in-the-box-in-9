import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 139 = true ∨ valuation q 19 = true ∨ valuation q 23 = true := by
  rw [value19, value20, value23, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(130 : Vertex), (135 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (195 : Vertex) [(130 : Vertex), (135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value21, value22, value27, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (134 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value27, value30, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (132 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 140 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value21, value27, value30, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(140 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (134 : Vertex) [(140 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 140 = true ∨ valuation q 22 = true ∨ valuation q 30 = true := by
  rw [value21, value22, value30, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(134 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (140 : Vertex) [(134 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 140 = true ∨ valuation q 22 = true ∨ valuation q 27 = true := by
  rw [value21, value22, value27, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(134 : Vertex), (140 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (148 : Vertex) [(134 : Vertex), (140 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value19, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (132 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 28 = false := by
  rw [value19, value21, value22, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (132 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 28 = false := by
  rw [value19, value22, value23, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (135 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 28 = false := by
  rw [value21, value22, value23, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (135 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 141 = true ∨ valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 28 = true ∨ valuation q 88 = true := by
  rw [value21, value22, value23, value28, value88, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(132 : Vertex), (135 : Vertex), (142 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (130 : Vertex) [(132 : Vertex), (135 : Vertex), (142 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 141 = true ∨ valuation q 19 = true ∨ valuation q 23 = true ∨ valuation q 28 = true ∨ valuation q 88 = true := by
  rw [value19, value22, value23, value28, value88, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(130 : Vertex), (135 : Vertex), (142 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (132 : Vertex) [(130 : Vertex), (135 : Vertex), (142 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 141 = true ∨ valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 28 = true ∨ valuation q 88 = true := by
  rw [value19, value21, value22, value28, value88, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(130 : Vertex), (132 : Vertex), (142 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (135 : Vertex) [(130 : Vertex), (132 : Vertex), (142 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 141 = true ∨ valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 28 = true := by
  rw [value19, value21, value22, value23, value28, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(130 : Vertex), (132 : Vertex), (135 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (390 : Vertex) [(130 : Vertex), (132 : Vertex), (135 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 32 = false := by
  rw [value20, value22, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 89 = false := by
  rw [value20, value22, value23, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 20 = false ∨ valuation q 32 = false ∨ valuation q 42 = false := by
  rw [value20, value23, value32, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (151 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 20 = false ∨ valuation q 32 = false ∨ valuation q 89 = false := by
  rw [value20, value23, value32, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (151 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 20 = false ∨ valuation q 42 = false ∨ valuation q 89 = false := by
  rw [value20, value23, value42, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 32 = false ∨ valuation q 42 = false := by
  rw [value22, value23, value32, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (151 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 32 = false ∨ valuation q 89 = false := by
  rw [value22, value23, value32, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (151 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 42 = false ∨ valuation q 89 = false := by
  rw [value22, value23, value42, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 42 = false ∨ valuation q 89 = false := by
  rw [value23, value32, value42, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (151 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value24, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 90 = false := by
  rw [value24, value25, value26, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 90 = false := by
  rw [value24, value25, value27, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (140 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 90 = false := by
  rw [value24, value26, value27, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 144 = true ∨ valuation q 33 = true ∨ valuation q 43 = true ∨ valuation q 91 = true := by
  rw [value25, value33, value43, value91, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(153 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (136 : Vertex) [(153 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 144 = true ∨ valuation q 24 = true ∨ valuation q 43 = true ∨ valuation q 91 = true := by
  rw [value24, value25, value43, value91, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(136 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (153 : Vertex) [(136 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 144 = true ∨ valuation q 24 = true ∨ valuation q 33 = true ∨ valuation q 91 = true := by
  rw [value24, value25, value33, value91, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (201 : Vertex) [(136 : Vertex), (153 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 144 = true ∨ valuation q 24 = true ∨ valuation q 33 = true ∨ valuation q 43 = true := by
  rw [value24, value25, value33, value43, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(136 : Vertex), (153 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 34 = false := by
  rw [value19, value24, value26, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (130 : Vertex) (136 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E078.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112078
