import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 13 = true := by
  rw [value13, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(21 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (55 : Vertex) [(21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 71 = true := by
  rw [value31, value71, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(183 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (53 : Vertex) [(183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 30 = true := by
  rw [value30, value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(53 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (183 : Vertex) [(53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 24 = false ∨ valuation q 33 = false ∨ valuation q 73 = false := by
  rw [value24, value32, value33, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (59 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 33 = true ∨ valuation q 73 = true := by
  rw [value32, value33, value73, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(59 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (41 : Vertex) [(59 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 24 = true ∨ valuation q 73 = true := by
  rw [value24, value32, value73, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(41 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (59 : Vertex) [(41 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 24 = true ∨ valuation q 33 = true := by
  rw [value24, value32, value33, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(41 : Vertex), (59 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (185 : Vertex) [(41 : Vertex), (59 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 16 = false ∨ valuation q 32 = false ∨ valuation q 75 = false := by
  rw [value16, value32, value33, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (59 : Vertex) (27 : Vertex) (57 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 16 = false ∨ valuation q 32 = false := by
  rw [value16, value32, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (59 : Vertex) (27 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 16 = false ∨ valuation q 75 = false := by
  rw [value16, value75, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (59 : Vertex) (27 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 149 = true ∨ valuation q 32 = true ∨ valuation q 75 = true := by
  rw [value32, value33, value75, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(57 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (27 : Vertex) [(57 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 149 = true ∨ valuation q 16 = true ∨ valuation q 75 = true := by
  rw [value16, value33, value75, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(27 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (57 : Vertex) [(27 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 17 = false ∨ valuation q 35 = false ∨ valuation q 76 = false := by
  rw [value17, value34, value35, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (60 : Vertex) (28 : Vertex) (62 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 35 = true ∨ valuation q 76 = true := by
  rw [value34, value35, value76, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (60 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(62 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (60 : Vertex) (28 : Vertex) [(62 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 17 = true ∨ valuation q 76 = true := by
  rw [value17, value34, value76, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (60 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(28 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (60 : Vertex) (62 : Vertex) [(28 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 17 = true ∨ valuation q 35 = true := by
  rw [value17, value34, value35, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (60 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(28 : Vertex), (62 : Vertex)] := by decide
  have hg := other_cover q (60 : Vertex) (188 : Vertex) [(28 : Vertex), (62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = true := by
  rw [value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ∈ [(60 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (62 : Vertex) [(60 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 151 = true := by
  rw [value35, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (60 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (62 : Vertex) (60 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 1 = true ∨ valuation q 46 = true := by
  rw [value1, value36, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (128 : Vertex) w → w ∈ region → w ∈ [(0 : Vertex), (144 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (128 : Vertex) [(0 : Vertex), (144 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 152 = true ∨ valuation q 46 = true := by
  rw [value36, value46, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (128 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (128 : Vertex) (0 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 152 = true ∨ valuation q 1 = true := by
  rw [value1, value36, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (128 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (128 : Vertex) (144 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 2 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value2, value37, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (135 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 2 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value2, value37, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (135 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 2 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value2, value37, value42, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value37, value40, value42, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (135 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 2 = true ∨ valuation q 42 = true ∨ valuation q 48 = true := by
  rw [value2, value37, value42, value48, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(3 : Vertex), (139 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(3 : Vertex), (139 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 44 = false ∨ valuation q 49 = false := by
  rw [value38, value40, value44, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 44 = false ∨ valuation q 59 = false := by
  rw [value38, value40, value44, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (141 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 59 = false := by
  rw [value38, value40, value49, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (149 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 44 = false ∨ valuation q 49 = false ∨ valuation q 59 = false := by
  rw [value38, value44, value49, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (141 : Vertex) (149 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 44 = true ∨ valuation q 49 = true ∨ valuation q 59 = true := by
  rw [value38, value44, value49, value59, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(141 : Vertex), (149 : Vertex), (165 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (135 : Vertex) [(141 : Vertex), (149 : Vertex), (165 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 40 = true ∨ valuation q 44 = true ∨ valuation q 59 = true := by
  rw [value38, value40, value44, value59, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(135 : Vertex), (141 : Vertex), (165 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (149 : Vertex) [(135 : Vertex), (141 : Vertex), (165 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E257.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112257
