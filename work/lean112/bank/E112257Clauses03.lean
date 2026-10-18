import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 20 = true ∨ valuation q 24 = true := by
  rw [value19, value20, value24, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(35 : Vertex), (41 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (161 : Vertex) [(35 : Vertex), (41 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 2 = true ∨ valuation q 19 = true := by
  rw [value2, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ∈ [(3 : Vertex), (33 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (35 : Vertex) [(3 : Vertex), (33 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 19 = true := by
  rw [value19, value20, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(33 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (3 : Vertex) [(33 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 2 = true := by
  rw [value2, value20, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (35 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(3 : Vertex)] := by decide
  have hg := other_cover q (35 : Vertex) (33 : Vertex) [(3 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 22 = true := by
  rw [value21, value22, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(38 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (4 : Vertex) [(38 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 3 = true := by
  rw [value3, value21, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(4 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (38 : Vertex) [(4 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true ∨ valuation q 21 = true ∨ valuation q 60 = true := by
  rw [value21, value22, value60, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(36 : Vertex), (166 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (6 : Vertex) [(36 : Vertex), (166 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true ∨ valuation q 4 = true ∨ valuation q 60 = true := by
  rw [value4, value22, value60, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(6 : Vertex), (166 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (36 : Vertex) [(6 : Vertex), (166 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true ∨ valuation q 4 = true ∨ valuation q 21 = true := by
  rw [value4, value21, value22, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(6 : Vertex), (36 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (166 : Vertex) [(6 : Vertex), (36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 25 = true ∨ valuation q 61 = true := by
  rw [value23, value25, value61, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(42 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (41 : Vertex) [(42 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 24 = true ∨ valuation q 61 = true := by
  rw [value23, value24, value61, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(41 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (42 : Vertex) [(41 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 24 = true ∨ valuation q 25 = true := by
  rw [value23, value24, value25, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(41 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (168 : Vertex) [(41 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 23 = false := by
  rw [value6, value19, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (33 : Vertex) (40 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 26 = false := by
  rw [value6, value19, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (33 : Vertex) (45 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 32 = false := by
  rw [value6, value19, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (33 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 62 = false := by
  rw [value6, value19, value24, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (33 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 89 = false := by
  rw [value6, value19, value24, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (33 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value6, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (40 : Vertex) (45 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value6, value23, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (40 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 62 = false := by
  rw [value6, value23, value24, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (40 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 89 = false := by
  rw [value6, value23, value24, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (40 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value6, value24, value26, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (45 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 62 = false := by
  rw [value6, value24, value26, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (45 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 32 = false ∨ valuation q 62 = false := by
  rw [value6, value24, value32, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (57 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 32 = false ∨ valuation q 89 = false := by
  rw [value6, value24, value32, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (57 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value6, value24, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (9 : Vertex) (169 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value19, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (40 : Vertex) (45 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value19, value23, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (40 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 62 = false := by
  rw [value19, value23, value24, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (40 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 89 = false := by
  rw [value19, value23, value24, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (40 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value19, value24, value26, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (45 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 26 = false ∨ valuation q 62 = false := by
  rw [value19, value24, value26, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (45 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E257.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112257
