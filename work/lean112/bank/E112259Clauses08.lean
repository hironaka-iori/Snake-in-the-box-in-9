import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 2 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value2, value56, value62, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 2 = false ∨ valuation q 62 = false ∨ valuation q 78 = false := by
  rw [value2, value56, value62, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (139 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 2 = false ∨ valuation q 66 = false ∨ valuation q 78 = false := by
  rw [value2, value56, value66, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (3 : Vertex) (147 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value55, value56, value62, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (129 : Vertex) (139 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 62 = false ∨ valuation q 78 = false := by
  rw [value55, value56, value62, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (129 : Vertex) (139 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 66 = false ∨ valuation q 78 = false := by
  rw [value55, value56, value66, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (129 : Vertex) (147 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 78 = false := by
  rw [value56, value62, value66, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (139 : Vertex) (147 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 2 = false ∨ valuation q 62 = false := by
  rw [value2, value62, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (131 : Vertex) (3 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 172 = true ∨ valuation q 55 = true ∨ valuation q 62 = true ∨ valuation q 66 = true ∨ valuation q 78 = true := by
  rw [value55, value56, value62, value66, value78, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (3 : Vertex) → w ∈ [(129 : Vertex), (139 : Vertex), (147 : Vertex), (163 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (3 : Vertex) [(129 : Vertex), (139 : Vertex), (147 : Vertex), (163 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 172 = true ∨ valuation q 2 = true ∨ valuation q 55 = true ∨ valuation q 66 = true ∨ valuation q 78 = true := by
  rw [value2, value55, value56, value66, value78, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(3 : Vertex), (129 : Vertex), (147 : Vertex), (163 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (139 : Vertex) [(3 : Vertex), (129 : Vertex), (147 : Vertex), (163 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 3 = false ∨ valuation q 54 = false ∨ valuation q 67 = false := by
  rw [value3, value54, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (128 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 3 = false ∨ valuation q 54 = false ∨ valuation q 79 = false := by
  rw [value3, value54, value57, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (128 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 3 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value3, value57, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (133 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 3 = false ∨ valuation q 58 = false ∨ valuation q 67 = false := by
  rw [value3, value57, value58, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (133 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 3 = false ∨ valuation q 58 = false ∨ valuation q 79 = false := by
  rw [value3, value57, value58, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (133 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 3 = false ∨ valuation q 59 = false ∨ valuation q 67 = false := by
  rw [value3, value57, value59, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (134 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 3 = false ∨ valuation q 59 = false ∨ valuation q 79 = false := by
  rw [value3, value57, value59, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (134 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 3 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value3, value57, value67, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (4 : Vertex) (148 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value57, value58, value67, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (148 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value57, value59, value67, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (134 : Vertex) (148 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 173 = true ∨ valuation q 3 = true ∨ valuation q 54 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 67 = true := by
  rw [value3, value54, value57, value58, value59, value67, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(4 : Vertex), (128 : Vertex), (133 : Vertex), (134 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (164 : Vertex) [(4 : Vertex), (128 : Vertex), (133 : Vertex), (134 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value55, value57, value58, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (132 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 68 = false := by
  rw [value55, value57, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (132 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value55, value58, value63, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value57, value58, value63, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 174 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 68 = true := by
  rw [value55, value57, value58, value68, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(129 : Vertex), (132 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (141 : Vertex) [(129 : Vertex), (132 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 174 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 63 = true := by
  rw [value55, value57, value58, value63, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(129 : Vertex), (132 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (149 : Vertex) [(129 : Vertex), (132 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 57 = false ∨ valuation q 64 = false ∨ valuation q 69 = false := by
  rw [value57, value59, value64, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (142 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 64 = false ∨ valuation q 69 = false := by
  rw [value64, value69, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (134 : Vertex) (142 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 57 = true ∨ valuation q 69 = true := by
  rw [value57, value59, value69, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(132 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (142 : Vertex) [(132 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 175 = true ∨ valuation q 57 = true ∨ valuation q 64 = true := by
  rw [value57, value59, value64, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(132 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (150 : Vertex) [(132 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 5 = false ∨ valuation q 61 = false ∨ valuation q 81 = false := by
  rw [value5, value60, value61, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (8 : Vertex) (137 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E259.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112259
