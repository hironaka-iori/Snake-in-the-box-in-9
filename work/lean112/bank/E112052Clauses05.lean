import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 22 = false ∨ valuation q 37 = false ∨ valuation q 117 = false := by
  rw [value22, value37, value39, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (142 : Vertex) (202 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 117 = false := by
  rw [value34, value37, value39, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (202 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 117 = false := by
  rw [value34, value38, value39, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 166 = true ∨ valuation q 22 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 38 = true := by
  rw [value22, value34, value37, value38, value39, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(142 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (462 : Vertex) [(142 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 24 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value24, value40, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (213 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ∈ [(213 : Vertex), (214 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (212 : Vertex) [(213 : Vertex), (214 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 43 = true := by
  rw [value41, value43, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(214 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (213 : Vertex) [(214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 42 = true := by
  rw [value41, value42, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(213 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (214 : Vertex) [(213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 48 = false := by
  rw [value40, value41, value42, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (209 : Vertex) (212 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 169 = true ∨ valuation q 41 = true ∨ valuation q 44 = true ∨ valuation q 48 = true := by
  rw [value41, value42, value44, value48, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(212 : Vertex), (215 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (209 : Vertex) [(212 : Vertex), (215 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 169 = true ∨ valuation q 40 = true ∨ valuation q 44 = true ∨ valuation q 48 = true := by
  rw [value40, value42, value44, value48, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(209 : Vertex), (215 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (212 : Vertex) [(209 : Vertex), (215 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 169 = true ∨ valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 44 = true := by
  rw [value40, value41, value42, value44, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(209 : Vertex), (212 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (221 : Vertex) [(209 : Vertex), (212 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 170 = true ∨ valuation q 41 = true ∨ valuation q 44 = true := by
  rw [value41, value43, value44, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(212 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (198 : Vertex) [(212 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 170 = true ∨ valuation q 34 = true ∨ valuation q 44 = true := by
  rw [value34, value43, value44, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(198 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (212 : Vertex) [(198 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 170 = true ∨ valuation q 34 = true ∨ valuation q 41 = true := by
  rw [value34, value41, value43, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(198 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (215 : Vertex) [(198 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 27 = false ∨ valuation q 35 = false := by
  rw [value7, value27, value35, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (151 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 27 = false ∨ valuation q 42 = false := by
  rw [value7, value27, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (151 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 27 = false ∨ valuation q 43 = false := by
  rw [value7, value27, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (151 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 27 = false ∨ valuation q 122 = false := by
  rw [value7, value27, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (151 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value7, value35, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (199 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 35 = false ∨ valuation q 43 = false := by
  rw [value7, value35, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 35 = false ∨ valuation q 122 = false := by
  rw [value7, value35, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (199 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value7, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 42 = false ∨ valuation q 122 = false := by
  rw [value7, value42, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (213 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 7 = false ∨ valuation q 43 = false ∨ valuation q 122 = false := by
  rw [value7, value43, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (87 : Vertex) (214 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 27 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value27, value35, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (199 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 27 = false ∨ valuation q 35 = false ∨ valuation q 43 = false := by
  rw [value27, value35, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 27 = false ∨ valuation q 35 = false ∨ valuation q 122 = false := by
  rw [value27, value35, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (199 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 27 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value27, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 27 = false ∨ valuation q 42 = false ∨ valuation q 122 = false := by
  rw [value27, value42, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (213 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 27 = false ∨ valuation q 43 = false ∨ valuation q 122 = false := by
  rw [value27, value43, value44, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (151 : Vertex) (214 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value35, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E052.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112052
