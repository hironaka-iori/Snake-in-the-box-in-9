import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 166 = true ∨ valuation q 36 = true ∨ valuation q 43 = true ∨ valuation q 47 = true := by
  rw [value36, value39, value43, value47, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(192 : Vertex), (204 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (228 : Vertex) [(192 : Vertex), (204 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value5, value36, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 36 = false ∨ valuation q 42 = false := by
  rw [value5, value36, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 36 = false ∨ valuation q 43 = false := by
  rw [value5, value36, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value5, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (201 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value5, value40, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (201 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 5 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value5, value40, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (202 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value36, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (201 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value36, value40, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (201 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value36, value40, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (202 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value40, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (201 : Vertex) (202 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 167 = true ∨ valuation q 36 = true ∨ valuation q 41 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value36, value40, value41, value42, value43, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(192 : Vertex), (201 : Vertex), (202 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (72 : Vertex) [(192 : Vertex), (201 : Vertex), (202 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 167 = true ∨ valuation q 5 = true ∨ valuation q 36 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value5, value36, value40, value42, value43, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(72 : Vertex), (192 : Vertex), (202 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(72 : Vertex), (192 : Vertex), (202 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 41 = true := by
  rw [value41, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (201 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 6 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 50 = true := by
  rw [value6, value37, value40, value41, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ∈ [(73 : Vertex), (193 : Vertex), (200 : Vertex), (217 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (201 : Vertex) [(73 : Vertex), (193 : Vertex), (200 : Vertex), (217 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 50 = false := by
  rw [value37, value40, value41, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value37, value40, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 50 = true := by
  rw [value37, value40, value41, value50, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(193 : Vertex), (200 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (73 : Vertex) [(193 : Vertex), (200 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 6 = true ∨ valuation q 40 = true ∨ valuation q 50 = true := by
  rw [value6, value40, value41, value50, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(73 : Vertex), (200 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (193 : Vertex) [(73 : Vertex), (200 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 6 = true ∨ valuation q 37 = true ∨ valuation q 50 = true := by
  rw [value6, value37, value41, value50, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(73 : Vertex), (193 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (200 : Vertex) [(73 : Vertex), (193 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 6 = true ∨ valuation q 37 = true ∨ valuation q 40 = true := by
  rw [value6, value37, value40, value41, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(73 : Vertex), (193 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (217 : Vertex) [(73 : Vertex), (193 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 51 = false := by
  rw [value38, value40, value42, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (200 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 59 = false := by
  rw [value38, value40, value42, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (200 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 51 = false ∨ valuation q 59 = false := by
  rw [value38, value42, value51, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (218 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value38, value42, value51, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (218 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 59 = false ∨ valuation q 102 = false := by
  rw [value38, value42, value59, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (234 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 40 = false ∨ valuation q 51 = false ∨ valuation q 59 = false := by
  rw [value40, value42, value51, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (200 : Vertex) (218 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 38 = false ∨ valuation q 51 = false := by
  rw [value38, value51, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (202 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 40 = false ∨ valuation q 51 = false := by
  rw [value40, value51, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (202 : Vertex) (200 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 169 = true ∨ valuation q 40 = true ∨ valuation q 51 = true ∨ valuation q 59 = true ∨ valuation q 102 = true := by
  rw [value40, value42, value51, value59, value102, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(200 : Vertex), (218 : Vertex), (234 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (194 : Vertex) [(200 : Vertex), (218 : Vertex), (234 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 169 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 51 = true ∨ valuation q 59 = true := by
  rw [value38, value40, value42, value51, value59, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(194 : Vertex), (200 : Vertex), (218 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (458 : Vertex) [(194 : Vertex), (200 : Vertex), (218 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 43 = true := by
  rw [value43, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (204 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block8 (q : Snake 81) (h : Conditions q) : B112E256.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112256
