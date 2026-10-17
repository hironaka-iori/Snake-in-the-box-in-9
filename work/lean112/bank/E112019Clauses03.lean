import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 27 = false ∨ valuation q 34 = false := by
  rw [value23, value24, value27, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (130 : Vertex) (135 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 34 = false := by
  rw [value23, value24, value29, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (130 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 34 = false := by
  rw [value24, value27, value29, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (135 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 145 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 34 = true := by
  rw [value24, value27, value29, value34, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(135 : Vertex), (139 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 145 = true ∨ valuation q 23 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value23, value24, value27, value29, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(130 : Vertex), (135 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (147 : Vertex) [(130 : Vertex), (135 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 2 = false ∨ valuation q 26 = false ∨ valuation q 35 = false := by
  rw [value2, value25, value26, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (133 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 2 = false ∨ valuation q 26 = false ∨ valuation q 82 = false := by
  rw [value2, value25, value26, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (133 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 35 = false ∨ valuation q 82 = false := by
  rw [value25, value26, value35, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (148 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 83 = false := by
  rw [value25, value26, value27, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 25 = false ∨ valuation q 30 = false ∨ valuation q 83 = false := by
  rw [value25, value26, value30, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (141 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 147 = true ∨ valuation q 27 = true ∨ valuation q 30 = true ∨ valuation q 83 = true := by
  rw [value26, value27, value30, value83, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(135 : Vertex), (141 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (132 : Vertex) [(135 : Vertex), (141 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 147 = true ∨ valuation q 25 = true ∨ valuation q 30 = true ∨ valuation q 83 = true := by
  rw [value25, value26, value30, value83, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(132 : Vertex), (141 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (135 : Vertex) [(132 : Vertex), (141 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 147 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 83 = true := by
  rw [value25, value26, value27, value83, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(132 : Vertex), (135 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (141 : Vertex) [(132 : Vertex), (135 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 147 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value25, value26, value27, value30, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(132 : Vertex), (135 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (389 : Vertex) [(132 : Vertex), (135 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 31 = false := by
  rw [value24, value26, value27, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 43 = false := by
  rw [value24, value26, value27, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 31 = false ∨ valuation q 43 = false := by
  rw [value24, value27, value31, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 43 = false := by
  rw [value26, value27, value31, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (133 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 148 = true ∨ valuation q 24 = true ∨ valuation q 31 = true ∨ valuation q 43 = true := by
  rw [value24, value27, value31, value43, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(131 : Vertex), (143 : Vertex), (199 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (133 : Vertex) [(131 : Vertex), (143 : Vertex), (199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 148 = true ∨ valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 31 = true := by
  rw [value24, value26, value27, value31, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(131 : Vertex), (133 : Vertex), (143 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (199 : Vertex) [(131 : Vertex), (133 : Vertex), (143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 149 = true ∨ valuation q 23 = true ∨ valuation q 29 = true ∨ valuation q 86 = true := by
  rw [value23, value28, value29, value86, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(130 : Vertex), (139 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (10 : Vertex) [(130 : Vertex), (139 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 149 = true ∨ valuation q 3 = true ∨ valuation q 29 = true ∨ valuation q 86 = true := by
  rw [value3, value28, value29, value86, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(10 : Vertex), (139 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (130 : Vertex) [(10 : Vertex), (139 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value24, value28, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 46 = false := by
  rw [value24, value28, value29, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 87 = false := by
  rw [value24, value28, value29, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 31 = false ∨ valuation q 46 = false := by
  rw [value24, value29, value31, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 31 = false ∨ valuation q 87 = false := by
  rw [value24, value29, value31, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 46 = false ∨ valuation q 87 = false := by
  rw [value24, value29, value46, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 87 = false := by
  rw [value28, value29, value31, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 28 = false ∨ valuation q 46 = false ∨ valuation q 87 = false := by
  rw [value28, value29, value46, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 46 = false ∨ valuation q 87 = false := by
  rw [value29, value31, value46, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (143 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 150 = true ∨ valuation q 24 = true ∨ valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 87 = true := by
  rw [value24, value28, value29, value31, value87, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(131 : Vertex), (138 : Vertex), (143 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (203 : Vertex) [(131 : Vertex), (138 : Vertex), (143 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E019.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112019
