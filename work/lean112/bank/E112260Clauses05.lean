import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 27 = false := by
  rw [value19, value21, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (103 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 31 = false := by
  rw [value19, value21, value22, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (103 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 59 = false := by
  rw [value19, value21, value22, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (103 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 27 = false ∨ valuation q 31 = false := by
  rw [value19, value21, value27, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (110 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 27 = false ∨ valuation q 59 = false := by
  rw [value19, value21, value27, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (110 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 31 = false ∨ valuation q 59 = false := by
  rw [value19, value21, value31, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (98 : Vertex) (118 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 31 = false := by
  rw [value21, value22, value27, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (103 : Vertex) (110 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 31 = false ∨ valuation q 59 = false := by
  rw [value21, value27, value31, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (102 : Vertex) (110 : Vertex) (118 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 5 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value5, value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (103 : Vertex) (71 : Vertex) (101 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 96 = false := by
  rw [value20, value21, value22, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (103 : Vertex) (101 : Vertex) (102 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 149 = true ∨ valuation q 5 = true ∨ valuation q 20 = true ∨ valuation q 21 = true := by
  rw [value5, value20, value21, value22, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(71 : Vertex), (101 : Vertex), (102 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (359 : Vertex) [(71 : Vertex), (101 : Vertex), (102 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value6, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (72 : Vertex) (105 : Vertex) (108 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value6, value23, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (72 : Vertex) (105 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 24 = false ∨ valuation q 60 = false := by
  rw [value6, value23, value24, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (72 : Vertex) (105 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value6, value23, value26, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (72 : Vertex) (108 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 60 = false := by
  rw [value6, value23, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (72 : Vertex) (108 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 32 = false ∨ valuation q 60 = false := by
  rw [value6, value23, value32, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (72 : Vertex) (120 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value23, value24, value26, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (105 : Vertex) (108 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 60 = false := by
  rw [value23, value24, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (105 : Vertex) (108 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 60 = false := by
  rw [value23, value24, value32, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (105 : Vertex) (120 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 32 = false ∨ valuation q 60 = false := by
  rw [value23, value26, value32, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (104 : Vertex) (108 : Vertex) (120 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 150 = true ∨ valuation q 6 = true ∨ valuation q 26 = true ∨ valuation q 32 = true ∨ valuation q 60 = true := by
  rw [value6, value23, value26, value32, value60, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(72 : Vertex), (108 : Vertex), (120 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (105 : Vertex) [(72 : Vertex), (108 : Vertex), (120 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 150 = true ∨ valuation q 6 = true ∨ valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 60 = true := by
  rw [value6, value23, value24, value26, value60, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(72 : Vertex), (105 : Vertex), (108 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (120 : Vertex) [(72 : Vertex), (105 : Vertex), (108 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 24 = true := by
  rw [value24, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (105 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = true ∨ valuation q 25 = true ∨ valuation q 61 = true := by
  rw [value23, value24, value25, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ∈ [(104 : Vertex), (107 : Vertex), (233 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (105 : Vertex) [(104 : Vertex), (107 : Vertex), (233 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 61 = false := by
  rw [value23, value24, value25, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (104 : Vertex) (107 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value23, value25, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (105 : Vertex) (104 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 23 = false ∨ valuation q 61 = false := by
  rw [value23, value61, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (105 : Vertex) (104 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 25 = true ∨ valuation q 61 = true := by
  rw [value24, value25, value61, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(107 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (104 : Vertex) [(107 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 23 = true ∨ valuation q 61 = true := by
  rw [value23, value24, value61, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(104 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (107 : Vertex) [(104 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 23 = true ∨ valuation q 25 = true := by
  rw [value23, value24, value25, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(104 : Vertex), (107 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (233 : Vertex) [(104 : Vertex), (107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 24 = false ∨ valuation q 62 = false := by
  rw [value7, value24, value25, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (75 : Vertex) (105 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E260.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112260
