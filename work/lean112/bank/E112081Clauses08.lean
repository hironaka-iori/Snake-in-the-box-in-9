import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 51 = false ∨ valuation q 63 = false ∨ valuation q 90 = false := by
  rw [value51, value52, value63, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 63 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value52, value63, value72, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (279 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 58 = true ∨ valuation q 72 = true ∨ valuation q 90 = true := by
  rw [value50, value51, value52, value58, value72, value90, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (271 : Vertex), (327 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (279 : Vertex) [(261 : Vertex), (262 : Vertex), (271 : Vertex), (327 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 58 = true ∨ valuation q 63 = true ∨ valuation q 72 = true := by
  rw [value50, value51, value52, value58, value63, value72, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (271 : Vertex), (279 : Vertex), (327 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (391 : Vertex) [(261 : Vertex), (262 : Vertex), (271 : Vertex), (279 : Vertex), (327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value4, value53, value54, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 54 = false ∨ valuation q 73 = false := by
  rw [value4, value53, value54, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 54 = false ∨ valuation q 91 = false := by
  rw [value4, value53, value54, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 56 = false ∨ valuation q 73 = false := by
  rw [value4, value53, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 56 = false ∨ valuation q 91 = false := by
  rw [value4, value53, value56, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (268 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 64 = false ∨ valuation q 91 = false := by
  rw [value4, value53, value64, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (280 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 4 = false ∨ valuation q 73 = false ∨ valuation q 91 = false := by
  rw [value4, value53, value73, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value46, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 64 = false := by
  rw [value46, value53, value54, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (266 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 64 = false := by
  rw [value46, value53, value56, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 46 = false ∨ valuation q 64 = false ∨ valuation q 73 = false := by
  rw [value46, value53, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 73 = false := by
  rw [value53, value54, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 73 = false := by
  rw [value53, value54, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 73 = false ∨ valuation q 91 = false := by
  rw [value53, value54, value73, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (266 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 73 = false := by
  rw [value53, value56, value64, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (268 : Vertex) (280 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 73 = false ∨ valuation q 91 = false := by
  rw [value53, value56, value73, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (268 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 64 = false ∨ valuation q 73 = false ∨ valuation q 91 = false := by
  rw [value53, value64, value73, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (280 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value48, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (264 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 57 = false := by
  rw [value48, value53, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (264 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 66 = false := by
  rw [value48, value53, value54, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (264 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 48 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value48, value54, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 48 = false ∨ valuation q 55 = false ∨ valuation q 66 = false := by
  rw [value48, value54, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (267 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 48 = false ∨ valuation q 57 = false ∨ valuation q 66 = false := by
  rw [value48, value54, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (270 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value53, value54, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (264 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 66 = false := by
  rw [value53, value54, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (264 : Vertex) (267 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 57 = false ∨ valuation q 66 = false := by
  rw [value53, value54, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (264 : Vertex) (270 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 66 = false := by
  rw [value54, value55, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (267 : Vertex) (270 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 48 = false ∨ valuation q 53 = false := by
  rw [value48, value53, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (266 : Vertex) (258 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E081.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112081
