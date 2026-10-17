import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 18 = true := by
  rw [value17, value18, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(131 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (137 : Vertex) [(131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 136 = true ∨ valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 27 = true := by
  rw [value18, value20, value22, value27, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (129 : Vertex) [(135 : Vertex), (139 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 136 = true ∨ valuation q 17 = true ∨ valuation q 20 = true ∨ valuation q 22 = true := by
  rw [value17, value18, value20, value22, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(129 : Vertex), (135 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (147 : Vertex) [(129 : Vertex), (135 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 1 = false ∨ valuation q 20 = false ∨ valuation q 79 = false := by
  rw [value1, value19, value20, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (135 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 1 = false ∨ valuation q 23 = false ∨ valuation q 79 = false := by
  rw [value1, value19, value23, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (142 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 20 = true ∨ valuation q 23 = true ∨ valuation q 79 = true := by
  rw [value19, value20, value23, value79, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(135 : Vertex), (142 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (6 : Vertex) [(135 : Vertex), (142 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 1 = true ∨ valuation q 20 = true ∨ valuation q 23 = true := by
  rw [value1, value19, value20, value23, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(6 : Vertex), (135 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (390 : Vertex) [(6 : Vertex), (135 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 24 = false := by
  rw [value18, value19, value20, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 80 = false := by
  rw [value18, value19, value20, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 37 = false := by
  rw [value18, value20, value24, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 80 = false := by
  rw [value18, value20, value24, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 37 = false ∨ valuation q 80 = false := by
  rw [value18, value20, value37, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 80 = false := by
  rw [value19, value20, value24, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (143 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 37 = false ∨ valuation q 80 = false := by
  rw [value19, value20, value37, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 37 = false ∨ valuation q 80 = false := by
  rw [value20, value24, value37, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (143 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 22 = true ∨ valuation q 82 = true := by
  rw [value21, value22, value82, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(139 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (129 : Vertex) [(139 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 17 = true ∨ valuation q 82 = true := by
  rw [value17, value21, value82, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(129 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (139 : Vertex) [(129 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 17 = true ∨ valuation q 22 = true := by
  rw [value17, value21, value22, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(129 : Vertex), (139 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(129 : Vertex), (139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value18, value21, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 39 = false := by
  rw [value18, value21, value22, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 39 = false := by
  rw [value18, value22, value24, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 39 = false := by
  rw [value21, value22, value24, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 86 = false := by
  rw [value19, value23, value24, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (143 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 19 = true ∨ valuation q 86 = true := by
  rw [value19, value23, value86, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(134 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (143 : Vertex) [(134 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 32 = false := by
  rw [value20, value22, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (135 : Vertex) (139 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value22, value23, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (139 : Vertex) (142 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value20, value22, value23, value24, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (159 : Vertex) [(135 : Vertex), (139 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value25, value26, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (146 : Vertex) (148 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 27 = true := by
  rw [value26, value27, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(147 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (144 : Vertex) [(147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 25 = true := by
  rw [value25, value26, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (147 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 26 = false ∨ valuation q 88 = false := by
  rw [value18, value26, value27, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (146 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 30 = true ∨ valuation q 46 = true := by
  rw [value29, value30, value46, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(156 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (144 : Vertex) [(156 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E096.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112096
