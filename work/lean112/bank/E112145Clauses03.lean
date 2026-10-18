import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 137 = true ∨ valuation q 32 = true := by
  rw [value32, value33, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(124 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (109 : Vertex) [(124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 137 = true ∨ valuation q 25 = true := by
  rw [value25, value33, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (124 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 32 = false := by
  rw [value30, value31, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (118 : Vertex) (122 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 138 = true ∨ valuation q 31 = true ∨ valuation q 32 = true := by
  rw [value31, value32, value34, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(122 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (118 : Vertex) [(122 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 139 = true ∨ valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 73 = true := by
  rw [value35, value36, value37, value40, value73, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (128 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(130 : Vertex), (132 : Vertex), (136 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (128 : Vertex) (0 : Vertex) [(130 : Vertex), (132 : Vertex), (136 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 139 = true ∨ valuation q 1 = true ∨ valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 40 = true := by
  rw [value1, value35, value36, value37, value40, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (128 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(0 : Vertex), (130 : Vertex), (132 : Vertex), (136 : Vertex)] := by decide
  have hg := other_cover q (128 : Vertex) (384 : Vertex) [(0 : Vertex), (130 : Vertex), (132 : Vertex), (136 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 42 = false := by
  rw [value35, value36, value38, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (128 : Vertex) (134 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 43 = false := by
  rw [value35, value37, value38, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (128 : Vertex) (134 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 45 = false := by
  rw [value35, value37, value38, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (128 : Vertex) (134 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value35, value37, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (128 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value37, value38, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (134 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 3 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value3, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (132 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 3 = false ∨ valuation q 37 = false ∨ valuation q 75 = false := by
  rw [value3, value37, value38, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (132 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 3 = false ∨ valuation q 44 = false ∨ valuation q 52 = false := by
  rw [value3, value38, value44, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (142 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value35, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (137 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value35, value40, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (137 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 77 = false := by
  rw [value35, value40, value41, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (137 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value35, value40, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 77 = false := by
  rw [value35, value40, value42, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (138 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 53 = false ∨ valuation q 77 = false := by
  rw [value35, value40, value53, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (200 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value40, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 146 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 49 = true := by
  rw [value36, value40, value42, value49, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(130 : Vertex), (136 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (142 : Vertex) [(130 : Vertex), (136 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 146 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 44 = true := by
  rw [value36, value40, value42, value44, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(130 : Vertex), (136 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (154 : Vertex) [(130 : Vertex), (136 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 44 = true := by
  rw [value37, value40, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ∈ [(132 : Vertex), (136 : Vertex), (142 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (140 : Vertex) [(132 : Vertex), (136 : Vertex), (142 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 147 = true ∨ valuation q 37 = true ∨ valuation q 40 = true := by
  rw [value37, value40, value43, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(132 : Vertex), (136 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (142 : Vertex) [(132 : Vertex), (136 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value38, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 149 = true ∨ valuation q 37 = true := by
  rw [value37, value45, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(132 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (149 : Vertex) [(132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 39 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value39, value46, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (135 : Vertex) (149 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 42 = false ∨ valuation q 50 = false ∨ valuation q 58 = false := by
  rw [value42, value49, value50, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 157 = true ∨ valuation q 54 = true ∨ valuation q 64 = true := by
  rw [value53, value54, value64, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(201 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (136 : Vertex) [(201 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 157 = true ∨ valuation q 40 = true ∨ valuation q 64 = true := by
  rw [value40, value53, value64, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(136 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(136 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 41 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value41, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E145.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112145
