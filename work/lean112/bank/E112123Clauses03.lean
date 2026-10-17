import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 32 = false := by
  rw [value9, value17, value19, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 79 = false := by
  rw [value9, value17, value19, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 32 = false := by
  rw [value9, value18, value19, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (30 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 32 = false ∨ valuation q 79 = false := by
  rw [value9, value19, value32, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (95 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 32 = false := by
  rw [value17, value18, value19, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (30 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 79 = false := by
  rw [value17, value18, value19, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (30 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 130 = true ∨ valuation q 23 = true := by
  rw [value20, value23, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(70 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (2 : Vertex) [(70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 130 = true ∨ valuation q 3 = true := by
  rw [value3, value20, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(2 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (70 : Vertex) [(2 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value21, value22, value23, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (69 : Vertex) (70 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 131 = true ∨ valuation q 23 = true ∨ valuation q 26 = true := by
  rw [value21, value23, value26, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(70 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (69 : Vertex) [(70 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 131 = true ∨ valuation q 22 = true ∨ valuation q 26 = true := by
  rw [value21, value22, value26, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (70 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 131 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value21, value22, value23, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(69 : Vertex), (70 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(69 : Vertex), (70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 5 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value5, value21, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (68 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 132 = true ∨ valuation q 5 = true ∨ valuation q 27 = true := by
  rw [value5, value22, value27, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(5 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (68 : Vertex) [(5 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value6, value20, value21, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (66 : Vertex) (68 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 133 = true ∨ valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 25 = true := by
  rw [value20, value21, value23, value25, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(66 : Vertex), (68 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (6 : Vertex) [(66 : Vertex), (68 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 133 = true ∨ valuation q 6 = true ∨ valuation q 21 = true ∨ valuation q 25 = true := by
  rw [value6, value21, value23, value25, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(6 : Vertex), (68 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (66 : Vertex) [(6 : Vertex), (68 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 134 = true ∨ valuation q 31 = true := by
  rw [value24, value31, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(91 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (11 : Vertex) [(91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 134 = true ∨ valuation q 7 = true := by
  rw [value7, value24, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(11 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (91 : Vertex) [(11 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 135 = true := by
  rw [value25, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (78 : Vertex) (70 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 136 = true ∨ valuation q 27 = true := by
  rw [value26, value27, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (68 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 137 = true ∨ valuation q 22 = true ∨ valuation q 28 = true := by
  rw [value22, value27, value28, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(69 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (84 : Vertex) [(69 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 138 = true ∨ valuation q 32 = true := by
  rw [value28, value32, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (85 : Vertex) [(95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 138 = true ∨ valuation q 27 = true := by
  rw [value27, value28, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (95 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 139 = true := by
  rw [value29, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (89 : Vertex) (91 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 140 = true := by
  rw [value30, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (90 : Vertex) (91 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value24, value32, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (91 : Vertex) (75 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 141 = true ∨ valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 32 = true := by
  rw [value29, value30, value31, value32, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(89 : Vertex), (90 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (75 : Vertex) [(89 : Vertex), (90 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 141 = true ∨ valuation q 24 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value24, value29, value30, value31, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(75 : Vertex), (89 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (95 : Vertex) [(75 : Vertex), (89 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value19, value28, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (31 : Vertex) (87 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 142 = true ∨ valuation q 19 = true ∨ valuation q 31 = true := by
  rw [value19, value31, value32, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(31 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (87 : Vertex) [(31 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 142 = true ∨ valuation q 19 = true ∨ valuation q 28 = true := by
  rw [value19, value28, value32, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(31 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (91 : Vertex) [(31 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E123.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112123
