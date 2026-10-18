import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 41 = false := by
  rw [value1, value6, value14, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (89 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 78 = false := by
  rw [value1, value6, value14, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (89 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 23 = false ∨ valuation q 41 = false := by
  rw [value1, value6, value23, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (105 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 23 = false ∨ valuation q 78 = false := by
  rw [value1, value6, value23, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (105 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 41 = false ∨ valuation q 78 = false := by
  rw [value1, value6, value41, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (201 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 14 = false := by
  rw [value5, value6, value7, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (75 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 23 = false := by
  rw [value5, value6, value7, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (75 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 41 = false := by
  rw [value5, value6, value7, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (75 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 78 = false := by
  rw [value5, value6, value7, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (75 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value5, value6, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (89 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 41 = false := by
  rw [value5, value6, value14, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (89 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 78 = false := by
  rw [value5, value6, value14, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (89 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 23 = false ∨ valuation q 41 = false := by
  rw [value5, value6, value23, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (105 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 23 = false ∨ valuation q 78 = false := by
  rw [value5, value6, value23, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (105 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 5 = false ∨ valuation q 41 = false ∨ valuation q 78 = false := by
  rw [value5, value6, value41, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (72 : Vertex) (201 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value6, value7, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (75 : Vertex) (89 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 41 = false := by
  rw [value6, value7, value14, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (75 : Vertex) (89 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 78 = false := by
  rw [value6, value7, value14, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (75 : Vertex) (89 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 41 = false := by
  rw [value6, value7, value23, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (75 : Vertex) (105 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 78 = false := by
  rw [value6, value7, value23, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (75 : Vertex) (105 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 41 = false ∨ valuation q 78 = false := by
  rw [value6, value7, value41, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (75 : Vertex) (201 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 23 = false ∨ valuation q 41 = false := by
  rw [value6, value14, value23, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (89 : Vertex) (105 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 23 = false ∨ valuation q 78 = false := by
  rw [value6, value14, value23, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (89 : Vertex) (105 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 78 = false := by
  rw [value6, value14, value41, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (89 : Vertex) (201 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 41 = false ∨ valuation q 78 = false := by
  rw [value6, value23, value41, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (105 : Vertex) (201 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 7 = true := by
  rw [value7, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (75 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 24 = true := by
  rw [value6, value7, value9, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ∈ [(73 : Vertex), (79 : Vertex), (107 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (75 : Vertex) [(73 : Vertex), (79 : Vertex), (107 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 9 = false ∨ valuation q 24 = false := by
  rw [value6, value7, value9, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (73 : Vertex) (79 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 9 = false ∨ valuation q 24 = false := by
  rw [value9, value24, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (75 : Vertex) (79 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 134 = true ∨ valuation q 9 = true ∨ valuation q 24 = true := by
  rw [value7, value9, value24, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(79 : Vertex), (107 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (73 : Vertex) [(79 : Vertex), (107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 134 = true ∨ valuation q 6 = true ∨ valuation q 24 = true := by
  rw [value6, value7, value24, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(73 : Vertex), (107 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (79 : Vertex) [(73 : Vertex), (107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 134 = true ∨ valuation q 6 = true ∨ valuation q 9 = true := by
  rw [value6, value7, value9, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(73 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (107 : Vertex) [(73 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E256.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112256
