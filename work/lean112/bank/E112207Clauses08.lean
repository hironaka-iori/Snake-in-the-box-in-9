import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 70 = false ∨ valuation q 88 = false := by
  rw [value3, value50, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (326 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 167 = true ∨ valuation q 3 = true ∨ valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 56 = true ∨ valuation q 88 = true := by
  rw [value3, value47, value48, value50, value51, value56, value88, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(6 : Vertex), (258 : Vertex), (260 : Vertex), (263 : Vertex), (270 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (326 : Vertex) [(6 : Vertex), (258 : Vertex), (260 : Vertex), (263 : Vertex), (270 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 57 = false := by
  rw [value49, value50, value51, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 62 = false := by
  rw [value49, value50, value51, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 71 = false := by
  rw [value49, value50, value51, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 89 = false := by
  rw [value49, value50, value51, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 57 = false ∨ valuation q 62 = false := by
  rw [value49, value51, value57, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 57 = false ∨ valuation q 71 = false := by
  rw [value49, value51, value57, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 57 = false ∨ valuation q 89 = false := by
  rw [value49, value51, value57, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 62 = false ∨ valuation q 71 = false := by
  rw [value49, value51, value62, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value49, value51, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 62 = false := by
  rw [value50, value51, value57, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 89 = false := by
  rw [value50, value51, value57, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 62 = false ∨ valuation q 71 = false := by
  rw [value50, value51, value62, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value50, value51, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value50, value51, value71, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 71 = false := by
  rw [value51, value57, value62, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value51, value57, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 57 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value51, value57, value71, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value51, value62, value71, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (279 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 53 = false := by
  rw [value4, value45, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (256 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 55 = false := by
  rw [value4, value45, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (256 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 63 = false := by
  rw [value4, value45, value52, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (256 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 72 = false := by
  rw [value4, value45, value52, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (256 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 90 = false := by
  rw [value4, value45, value52, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (256 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value4, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 63 = false := by
  rw [value4, value52, value53, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 72 = false := by
  rw [value4, value52, value53, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 90 = false := by
  rw [value4, value52, value53, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value4, value52, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (268 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 55 = false ∨ valuation q 72 = false := by
  rw [value4, value52, value55, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value4, value52, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (268 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E207.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112207
