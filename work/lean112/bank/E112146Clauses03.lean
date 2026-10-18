import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 135 = true ∨ valuation q 19 = true := by
  rw [value19, value21, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(80 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (90 : Vertex) [(80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 136 = true ∨ valuation q 25 = true := by
  rw [value22, value25, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(92 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 136 = true ∨ valuation q 19 = true := by
  rw [value19, value22, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(80 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (92 : Vertex) [(80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 26 = false := by
  rw [value6, value13, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (26 : Vertex) (74 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 81 = false := by
  rw [value6, value13, value24, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (26 : Vertex) (74 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value6, value21, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (26 : Vertex) (82 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 60 = false := by
  rw [value6, value24, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (26 : Vertex) (94 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 60 = false ∨ valuation q 81 = false := by
  rw [value6, value24, value60, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (26 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 81 = false := by
  rw [value13, value21, value24, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (82 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 26 = false ∨ valuation q 60 = false := by
  rw [value13, value24, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (94 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 26 = false ∨ valuation q 81 = false := by
  rw [value13, value24, value26, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (94 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 13 = false ∨ valuation q 60 = false ∨ valuation q 81 = false := by
  rw [value13, value24, value60, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 60 = false := by
  rw [value21, value24, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (94 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 81 = false := by
  rw [value21, value24, value26, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (94 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 21 = false ∨ valuation q 60 = false ∨ valuation q 81 = false := by
  rw [value21, value24, value60, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 60 = false := by
  rw [value23, value24, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (94 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 60 = false ∨ valuation q 81 = false := by
  rw [value24, value26, value60, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (94 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 26 = false := by
  rw [value15, value22, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (76 : Vertex) (84 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 140 = true ∨ valuation q 17 = true ∨ valuation q 25 = true ∨ valuation q 27 = true := by
  rw [value17, value25, value26, value27, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(78 : Vertex), (92 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (90 : Vertex) [(78 : Vertex), (92 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 140 = true ∨ valuation q 17 = true ∨ valuation q 24 = true ∨ valuation q 27 = true := by
  rw [value17, value24, value26, value27, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(78 : Vertex), (90 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (92 : Vertex) [(78 : Vertex), (90 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 140 = true ∨ valuation q 17 = true ∨ valuation q 24 = true ∨ valuation q 25 = true := by
  rw [value17, value24, value25, value26, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(78 : Vertex), (90 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (95 : Vertex) [(78 : Vertex), (90 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 26 = false ∨ valuation q 83 = false := by
  rw [value18, value26, value27, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (94 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 39 = false := by
  rw [value28, value30, value31, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (133 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 39 = false := by
  rw [value28, value30, value33, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 39 = false := by
  rw [value28, value31, value33, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (133 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 142 = true ∨ valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 39 = true := by
  rw [value28, value30, value33, value39, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(131 : Vertex), (137 : Vertex), (145 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (133 : Vertex) [(131 : Vertex), (137 : Vertex), (145 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 142 = true ∨ valuation q 30 = true ∨ valuation q 31 = true ∨ valuation q 39 = true := by
  rw [value28, value30, value31, value39, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(131 : Vertex), (133 : Vertex), (145 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (137 : Vertex) [(131 : Vertex), (133 : Vertex), (145 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value29, value30, value40, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 40 = false ∨ valuation q 84 = false := by
  rw [value29, value30, value40, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 46 = false ∨ valuation q 84 = false := by
  rw [value29, value30, value46, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 84 = false := by
  rw [value29, value40, value46, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (146 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 47 = false := by
  rw [value28, value29, value30, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (129 : Vertex) (130 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E146.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112146
