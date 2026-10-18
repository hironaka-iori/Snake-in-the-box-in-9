import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value4, value52, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (268 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value4, value52, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value45, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value45, value52, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value52, value53, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 72 = false := by
  rw [value52, value53, value55, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value52, value53, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value52, value55, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (268 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 47 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value47, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (264 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 47 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value47, value52, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (264 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 47 = false ∨ valuation q 52 = false ∨ valuation q 65 = false := by
  rw [value47, value52, value53, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (264 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 47 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value47, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 47 = false ∨ valuation q 54 = false ∨ valuation q 65 = false := by
  rw [value47, value53, value54, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (267 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 47 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value47, value53, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (270 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (264 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 65 = false := by
  rw [value52, value53, value54, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (264 : Vertex) (267 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value52, value53, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (264 : Vertex) (270 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value53, value54, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (267 : Vertex) (270 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 170 = true ∨ valuation q 47 = true ∨ valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 65 = true := by
  rw [value47, value52, value53, value54, value65, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(258 : Vertex), (264 : Vertex), (267 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (270 : Vertex) [(258 : Vertex), (264 : Vertex), (267 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 5 = false ∨ valuation q 53 = false ∨ valuation q 66 = false := by
  rw [value5, value53, value54, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (266 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 5 = false ∨ valuation q 53 = false ∨ valuation q 74 = false := by
  rw [value5, value53, value54, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (266 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 5 = false ∨ valuation q 66 = false ∨ valuation q 92 = false := by
  rw [value5, value54, value66, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (283 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 57 = false ∨ valuation q 66 = false := by
  rw [value53, value54, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (266 : Vertex) (271 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 66 = false ∨ valuation q 92 = false := by
  rw [value53, value54, value66, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (266 : Vertex) (283 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 55 = true := by
  rw [value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (268 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 56 = true := by
  rw [value48, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ∈ [(260 : Vertex), (264 : Vertex), (270 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (268 : Vertex) [(260 : Vertex), (264 : Vertex), (270 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value48, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (264 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 172 = true ∨ valuation q 48 = true ∨ valuation q 56 = true := by
  rw [value48, value55, value56, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(260 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (264 : Vertex) [(260 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 172 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value48, value52, value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (264 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex), (264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value50, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 57 = false := by
  rw [value50, value53, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value53, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (266 : Vertex) (268 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E203.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112203
