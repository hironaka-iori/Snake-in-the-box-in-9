import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 83 = false := by
  rw [value3, value4, value5, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (70 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 14 = false := by
  rw [value3, value5, value9, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (79 : Vertex) (87 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 22 = false := by
  rw [value3, value5, value9, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (79 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = false ∨ valuation q 9 = false ∨ valuation q 41 = false := by
  rw [value3, value5, value9, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (79 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 22 = false := by
  rw [value3, value5, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (87 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 41 = false := by
  rw [value3, value5, value14, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (87 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = false ∨ valuation q 22 = false ∨ valuation q 41 = false := by
  rw [value3, value5, value22, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (103 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 14 = false := by
  rw [value4, value5, value9, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (70 : Vertex) (79 : Vertex) (87 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 22 = false := by
  rw [value4, value5, value9, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (70 : Vertex) (79 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 41 = false := by
  rw [value4, value5, value9, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (70 : Vertex) (79 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 22 = false := by
  rw [value4, value5, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (70 : Vertex) (87 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 41 = false := by
  rw [value4, value5, value14, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (70 : Vertex) (87 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 41 = false := by
  rw [value4, value5, value22, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (70 : Vertex) (103 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 22 = false := by
  rw [value5, value9, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (79 : Vertex) (87 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 41 = false := by
  rw [value5, value9, value14, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (79 : Vertex) (87 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 22 = false ∨ valuation q 41 = false := by
  rw [value5, value9, value22, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (79 : Vertex) (103 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 41 = false := by
  rw [value5, value14, value22, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (87 : Vertex) (103 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 132 = true ∨ valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 14 = true ∨ valuation q 41 = true ∨ valuation q 83 = true := by
  rw [value3, value4, value5, value9, value14, value41, value83, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(69 : Vertex), (70 : Vertex), (79 : Vertex), (87 : Vertex), (199 : Vertex), (327 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (103 : Vertex) [(69 : Vertex), (70 : Vertex), (79 : Vertex), (87 : Vertex), (199 : Vertex), (327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 6 = true := by
  rw [value6, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (72 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 84 = false := by
  rw [value6, value8, value23, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (76 : Vertex) (104 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 8 = false ∨ valuation q 84 = false := by
  rw [value8, value84, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (72 : Vertex) (76 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 133 = true ∨ valuation q 8 = true ∨ valuation q 23 = true := by
  rw [value6, value8, value23, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(76 : Vertex), (104 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (328 : Vertex) [(76 : Vertex), (104 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 7 = true := by
  rw [value7, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (75 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 9 = true ∨ valuation q 25 = true ∨ valuation q 43 = true := by
  rw [value7, value9, value25, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ∈ [(79 : Vertex), (107 : Vertex), (203 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (75 : Vertex) [(79 : Vertex), (107 : Vertex), (203 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 25 = false ∨ valuation q 43 = false := by
  rw [value7, value9, value25, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (79 : Vertex) (107 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 9 = false ∨ valuation q 25 = false := by
  rw [value9, value25, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (75 : Vertex) (79 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 134 = true ∨ valuation q 25 = true ∨ valuation q 43 = true := by
  rw [value7, value25, value43, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(107 : Vertex), (203 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (79 : Vertex) [(107 : Vertex), (203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 134 = true ∨ valuation q 9 = true ∨ valuation q 43 = true := by
  rw [value7, value9, value43, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(79 : Vertex), (203 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (107 : Vertex) [(79 : Vertex), (203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 134 = true ∨ valuation q 9 = true ∨ valuation q 25 = true := by
  rw [value7, value9, value25, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(79 : Vertex), (107 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (203 : Vertex) [(79 : Vertex), (107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 44 = false := by
  rw [value6, value8, value26, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (72 : Vertex) (108 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 26 = true ∨ valuation q 44 = true := by
  rw [value8, value26, value44, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(108 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (72 : Vertex) [(108 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 135 = true ∨ valuation q 6 = true ∨ valuation q 44 = true := by
  rw [value6, value8, value44, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(72 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (108 : Vertex) [(72 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E260.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112260
