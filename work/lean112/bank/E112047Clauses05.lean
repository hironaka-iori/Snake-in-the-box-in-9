import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 21 = true ∨ valuation q 26 = true ∨ valuation q 31 = true ∨ valuation q 47 = true := by
  rw [value21, value26, value29, value31, value47, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(138 : Vertex), (146 : Vertex), (158 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (410 : Vertex) [(138 : Vertex), (146 : Vertex), (158 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (148 : Vertex) [(158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 28 = true := by
  rw [value28, value30, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(148 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (158 : Vertex) [(148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 31 = true := by
  rw [value31, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (158 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value29, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (154 : Vertex) (156 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value29, value30, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (158 : Vertex) (154 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 149 = true ∨ valuation q 30 = true ∨ valuation q 32 = true := by
  rw [value30, value31, value32, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(156 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (154 : Vertex) [(156 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 149 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value29, value30, value31, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(154 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (159 : Vertex) [(154 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 31 = true := by
  rw [value31, value32, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(158 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (143 : Vertex) [(158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 23 = true := by
  rw [value23, value32, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(143 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 14 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value14, value33, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (128 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 151 = true ∨ valuation q 14 = true ∨ valuation q 37 = true := by
  rw [value14, value33, value37, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(128 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(128 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 34 = true := by
  rw [value34, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (193 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 8 = true ∨ valuation q 15 = true ∨ valuation q 33 = true ∨ valuation q 38 = true := by
  rw [value8, value15, value33, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ∈ [(65 : Vertex), (129 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (193 : Vertex) [(65 : Vertex), (129 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 33 = false := by
  rw [value8, value15, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 38 = false := by
  rw [value8, value15, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (129 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 8 = false ∨ valuation q 33 = false := by
  rw [value8, value33, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 8 = false ∨ valuation q 38 = false := by
  rw [value8, value38, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (193 : Vertex) (65 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 15 = true ∨ valuation q 33 = true ∨ valuation q 38 = true := by
  rw [value15, value33, value34, value38, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(129 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (65 : Vertex) [(129 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 8 = true ∨ valuation q 33 = true ∨ valuation q 38 = true := by
  rw [value8, value33, value34, value38, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(65 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (129 : Vertex) [(65 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 8 = true ∨ valuation q 15 = true ∨ valuation q 38 = true := by
  rw [value8, value15, value34, value38, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(65 : Vertex), (129 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (192 : Vertex) [(65 : Vertex), (129 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 43 = false := by
  rw [value35, value36, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (199 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 40 = true ∨ valuation q 43 = true := by
  rw [value35, value40, value43, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(206 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (199 : Vertex) [(206 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 36 = true ∨ valuation q 43 = true := by
  rw [value35, value36, value43, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(199 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (206 : Vertex) [(199 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 19 = false ∨ valuation q 35 = false ∨ valuation q 44 = false := by
  rw [value19, value35, value36, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (135 : Vertex) (198 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 154 = true ∨ valuation q 19 = true ∨ valuation q 44 = true := by
  rw [value19, value36, value44, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(135 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (198 : Vertex) [(135 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 154 = true ∨ valuation q 19 = true ∨ valuation q 35 = true := by
  rw [value19, value35, value36, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(135 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (215 : Vertex) [(135 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 10 = false ∨ valuation q 33 = false ∨ valuation q 39 = false := by
  rw [value10, value33, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 10 = false ∨ valuation q 33 = false ∨ valuation q 45 = false := by
  rw [value10, value33, value37, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 10 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value10, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (201 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 10 = false ∨ valuation q 39 = false ∨ valuation q 45 = false := by
  rw [value10, value37, value39, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 39 = false ∨ valuation q 45 = false := by
  rw [value33, value37, value39, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E047.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112047
