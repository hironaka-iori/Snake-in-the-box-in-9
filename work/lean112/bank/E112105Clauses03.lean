import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value13, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (67 : Vertex) (81 : Vertex) (82 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 59 = false := by
  rw [value13, value22, value24, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (67 : Vertex) (81 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 76 = false := by
  rw [value13, value22, value24, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (67 : Vertex) (81 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 59 = false := by
  rw [value13, value23, value24, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (67 : Vertex) (82 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 76 = false := by
  rw [value13, value23, value24, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (67 : Vertex) (82 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 59 = false ∨ valuation q 76 = false := by
  rw [value13, value24, value59, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (67 : Vertex) (211 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 59 = false := by
  rw [value22, value23, value24, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (81 : Vertex) (82 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 76 = false := by
  rw [value22, value23, value24, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (81 : Vertex) (82 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 59 = false ∨ valuation q 76 = false := by
  rw [value22, value24, value59, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (81 : Vertex) (211 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 59 = false ∨ valuation q 76 = false := by
  rw [value23, value24, value59, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (82 : Vertex) (211 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 77 = false := by
  rw [value14, value21, value25, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 21 = true ∨ valuation q 77 = true := by
  rw [value21, value25, value77, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(80 : Vertex), (340 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (68 : Vertex) [(80 : Vertex), (340 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 14 = true ∨ valuation q 77 = true := by
  rw [value14, value25, value77, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(68 : Vertex), (340 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(68 : Vertex), (340 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 14 = true ∨ valuation q 21 = true := by
  rw [value14, value21, value25, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(68 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (340 : Vertex) [(68 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 28 = true := by
  rw [value26, value28, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(94 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (82 : Vertex) [(94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 23 = true := by
  rw [value23, value26, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(82 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (94 : Vertex) [(82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 27 = true := by
  rw [value27, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (93 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = true ∨ valuation q 29 = true := by
  rw [value18, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ∈ [(77 : Vertex), (95 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (93 : Vertex) [(77 : Vertex), (95 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 29 = true := by
  rw [value27, value29, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(95 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (77 : Vertex) [(95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 18 = true := by
  rw [value18, value27, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(77 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (95 : Vertex) [(77 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 19 = false ∨ valuation q 26 = false ∨ valuation q 29 = false := by
  rw [value19, value26, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (94 : Vertex) (78 : Vertex) (90 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 152 = true ∨ valuation q 26 = true ∨ valuation q 29 = true := by
  rw [value26, value28, value29, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(90 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (78 : Vertex) [(90 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 152 = true ∨ valuation q 19 = true ∨ valuation q 29 = true := by
  rw [value19, value28, value29, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(78 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (90 : Vertex) [(78 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 152 = true ∨ valuation q 19 = true ∨ valuation q 26 = true := by
  rw [value19, value26, value28, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(78 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (95 : Vertex) [(78 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 20 = false ∨ valuation q 27 = false ∨ valuation q 28 = false := by
  rw [value20, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (93 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 20 = true ∨ valuation q 28 = true := by
  rw [value20, value28, value29, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(79 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (93 : Vertex) [(79 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 20 = true ∨ valuation q 27 = true := by
  rw [value20, value27, value29, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(79 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (94 : Vertex) [(79 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 40 = false := by
  rw [value30, value31, value33, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (133 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 40 = false := by
  rw [value30, value31, value35, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 40 = false := by
  rw [value30, value33, value35, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (133 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 154 = true ∨ valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 35 = true := by
  rw [value30, value31, value33, value35, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(131 : Vertex), (133 : Vertex), (137 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (145 : Vertex) [(131 : Vertex), (133 : Vertex), (137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 34 = true ∨ valuation q 36 = true := by
  rw [value31, value34, value36, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (129 : Vertex) [(135 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E105.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112105
