import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 138 = true ∨ valuation q 21 = true ∨ valuation q 80 = true := by
  rw [value20, value21, value80, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(135 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (141 : Vertex) [(135 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 138 = true ∨ valuation q 21 = true ∨ valuation q 24 = true := by
  rw [value20, value21, value24, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(135 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (389 : Vertex) [(135 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 25 = false := by
  rw [value19, value20, value21, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 37 = false := by
  rw [value19, value20, value21, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 37 = false := by
  rw [value19, value21, value25, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 20 = false ∨ valuation q 25 = false ∨ valuation q 37 = false := by
  rw [value20, value21, value25, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (133 : Vertex) (143 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 1 = false ∨ valuation q 18 = false ∨ valuation q 23 = false := by
  rw [value1, value18, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (10 : Vertex) (130 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 1 = false ∨ valuation q 18 = false ∨ valuation q 83 = false := by
  rw [value1, value18, value22, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (10 : Vertex) (130 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 1 = false ∨ valuation q 23 = false ∨ valuation q 83 = false := by
  rw [value1, value22, value23, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (10 : Vertex) (139 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 140 = true ∨ valuation q 18 = true ∨ valuation q 23 = true ∨ valuation q 83 = true := by
  rw [value18, value22, value23, value83, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(130 : Vertex), (139 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (10 : Vertex) [(130 : Vertex), (139 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 140 = true ∨ valuation q 1 = true ∨ valuation q 23 = true ∨ valuation q 83 = true := by
  rw [value1, value22, value23, value83, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(10 : Vertex), (139 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (130 : Vertex) [(10 : Vertex), (139 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 140 = true ∨ valuation q 1 = true ∨ valuation q 18 = true ∨ valuation q 83 = true := by
  rw [value1, value18, value22, value83, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(10 : Vertex), (130 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (139 : Vertex) [(10 : Vertex), (130 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value19, value22, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 40 = false := by
  rw [value19, value22, value23, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 84 = false := by
  rw [value19, value22, value23, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 40 = false := by
  rw [value19, value23, value25, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 84 = false := by
  rw [value19, value23, value25, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 40 = false ∨ valuation q 84 = false := by
  rw [value19, value23, value40, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 40 = false := by
  rw [value22, value23, value25, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (143 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 84 = false := by
  rw [value22, value23, value25, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (143 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 40 = false ∨ valuation q 84 = false := by
  rw [value22, value23, value40, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (138 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 40 = false ∨ valuation q 84 = false := by
  rw [value23, value25, value40, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (143 : Vertex) (203 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 40 = true ∨ valuation q 84 = true := by
  rw [value22, value23, value25, value40, value84, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(138 : Vertex), (143 : Vertex), (203 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (131 : Vertex) [(138 : Vertex), (143 : Vertex), (203 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 20 = false ∨ valuation q 25 = false := by
  rw [value20, value25, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (141 : Vertex) (133 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 25 = true := by
  rw [value24, value25, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(143 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (133 : Vertex) [(143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 20 = true := by
  rw [value20, value24, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(133 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (143 : Vertex) [(133 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 33 = false := by
  rw [value21, value23, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (135 : Vertex) (139 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 33 = false := by
  rw [value23, value24, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (139 : Vertex) (141 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 33 = true := by
  rw [value23, value24, value25, value33, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(139 : Vertex), (141 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (135 : Vertex) [(139 : Vertex), (141 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 33 = true := by
  rw [value21, value23, value25, value33, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (141 : Vertex) [(135 : Vertex), (139 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value21, value23, value24, value25, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(135 : Vertex), (139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (159 : Vertex) [(135 : Vertex), (139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value26, value27, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (145 : Vertex) (148 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E110.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112110
