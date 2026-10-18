import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value38, value39, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (232 : Vertex) (235 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 38 = true ∨ valuation q 41 = true ∨ valuation q 49 = true := by
  rw [value38, value39, value41, value49, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(232 : Vertex), (235 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (169 : Vertex) [(232 : Vertex), (235 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 17 = true ∨ valuation q 41 = true ∨ valuation q 49 = true := by
  rw [value17, value39, value41, value49, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(169 : Vertex), (235 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (232 : Vertex) [(169 : Vertex), (235 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 17 = true ∨ valuation q 38 = true ∨ valuation q 49 = true := by
  rw [value17, value38, value39, value49, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(169 : Vertex), (232 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (235 : Vertex) [(169 : Vertex), (232 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 17 = true ∨ valuation q 38 = true ∨ valuation q 41 = true := by
  rw [value17, value38, value39, value41, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(169 : Vertex), (232 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (249 : Vertex) [(169 : Vertex), (232 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 18 = false ∨ valuation q 38 = false := by
  rw [value4, value18, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (170 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 18 = false ∨ valuation q 43 = false := by
  rw [value4, value18, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (170 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 18 = false ∨ valuation q 50 = false := by
  rw [value4, value18, value40, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (170 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 18 = false ∨ valuation q 104 = false := by
  rw [value4, value18, value40, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (170 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 38 = false ∨ valuation q 41 = false := by
  rw [value4, value38, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (232 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 38 = false ∨ valuation q 43 = false := by
  rw [value4, value38, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (232 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 38 = false ∨ valuation q 50 = false := by
  rw [value4, value38, value40, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (232 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 38 = false ∨ valuation q 104 = false := by
  rw [value4, value38, value40, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (232 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value4, value40, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (235 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 41 = false ∨ valuation q 50 = false := by
  rw [value4, value40, value41, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (235 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 43 = false ∨ valuation q 50 = false := by
  rw [value4, value40, value43, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 43 = false ∨ valuation q 104 = false := by
  rw [value4, value40, value43, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (238 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 50 = false ∨ valuation q 104 = false := by
  rw [value4, value40, value50, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (250 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 18 = false ∨ valuation q 38 = false ∨ valuation q 43 = false := by
  rw [value18, value38, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (170 : Vertex) (232 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 18 = false ∨ valuation q 38 = false ∨ valuation q 104 = false := by
  rw [value18, value38, value40, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (170 : Vertex) (232 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 18 = false ∨ valuation q 43 = false ∨ valuation q 50 = false := by
  rw [value18, value40, value43, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (170 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value38, value40, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (232 : Vertex) (235 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 43 = false ∨ valuation q 50 = false := by
  rw [value38, value40, value43, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (232 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 50 = false := by
  rw [value40, value41, value43, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (235 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 43 = false ∨ valuation q 50 = false ∨ valuation q 104 = false := by
  rw [value40, value43, value50, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (238 : Vertex) (250 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value5, value19, value33, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (171 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 19 = false ∨ valuation q 39 = false := by
  rw [value5, value19, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (171 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 19 = false ∨ valuation q 40 = false := by
  rw [value5, value19, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (171 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 19 = false ∨ valuation q 51 = false := by
  rw [value5, value19, value41, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (171 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 19 = false ∨ valuation q 105 = false := by
  rw [value5, value19, value41, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (171 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 33 = false ∨ valuation q 39 = false := by
  rw [value5, value33, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (227 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 5 = false ∨ valuation q 33 = false ∨ valuation q 40 = false := by
  rw [value5, value33, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (107 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E088.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112088
