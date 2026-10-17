import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 22 = false ∨ valuation q 79 = false := by
  rw [value10, value21, value22, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (51 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value10, value21, value25, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (54 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 54 = false := by
  rw [value10, value21, value25, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (54 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 79 = false := by
  rw [value10, value21, value25, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (54 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 28 = false ∨ valuation q 54 = false := by
  rw [value10, value21, value28, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (58 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 28 = false ∨ valuation q 79 = false := by
  rw [value10, value21, value28, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (58 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 54 = false ∨ valuation q 79 = false := by
  rw [value10, value21, value54, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (178 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 54 = false := by
  rw [value21, value22, value25, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (51 : Vertex) (54 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 79 = false := by
  rw [value21, value22, value25, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (51 : Vertex) (54 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 54 = false ∨ valuation q 79 = false := by
  rw [value21, value22, value54, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (51 : Vertex) (178 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 54 = false := by
  rw [value21, value25, value28, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (54 : Vertex) (58 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 79 = false := by
  rw [value21, value25, value54, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (54 : Vertex) (178 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 6 = false ∨ valuation q 20 = false ∨ valuation q 26 = false := by
  rw [value6, value20, value22, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (19 : Vertex) (49 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 6 = false ∨ valuation q 20 = false ∨ valuation q 29 = false := by
  rw [value6, value20, value22, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (19 : Vertex) (49 : Vertex) (59 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value6, value21, value22, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (19 : Vertex) (50 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 29 = false := by
  rw [value6, value21, value22, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (19 : Vertex) (50 : Vertex) (59 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 55 = false := by
  rw [value6, value21, value22, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (19 : Vertex) (50 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 55 = false := by
  rw [value6, value22, value26, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (19 : Vertex) (55 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 6 = false ∨ valuation q 29 = false ∨ valuation q 55 = false := by
  rw [value6, value22, value29, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (19 : Vertex) (59 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 6 = false ∨ valuation q 55 = false ∨ valuation q 80 = false := by
  rw [value6, value22, value55, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (19 : Vertex) (179 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value20, value21, value22, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (49 : Vertex) (50 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 80 = false := by
  rw [value20, value21, value22, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (49 : Vertex) (50 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 26 = false ∨ valuation q 29 = false := by
  rw [value20, value22, value26, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (49 : Vertex) (55 : Vertex) (59 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 55 = false := by
  rw [value21, value22, value26, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (50 : Vertex) (55 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 55 = false := by
  rw [value21, value22, value29, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (50 : Vertex) (59 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 24 = false ∨ valuation q 81 = false := by
  rw [value11, value23, value24, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (52 : Vertex) (36 : Vertex) (53 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 23 = false := by
  rw [value12, value20, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (37 : Vertex) (49 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 26 = false := by
  rw [value12, value20, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (37 : Vertex) (49 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 20 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value20, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (49 : Vertex) (52 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 150 = true ∨ valuation q 20 = true ∨ valuation q 23 = true ∨ valuation q 26 = true := by
  rw [value20, value23, value24, value26, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(49 : Vertex), (52 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (37 : Vertex) [(49 : Vertex), (52 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 150 = true ∨ valuation q 12 = true ∨ valuation q 20 = true ∨ valuation q 26 = true := by
  rw [value12, value20, value24, value26, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (52 : Vertex) → w ∈ [(37 : Vertex), (49 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (52 : Vertex) [(37 : Vertex), (49 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 150 = true ∨ valuation q 12 = true ∨ valuation q 20 = true ∨ valuation q 23 = true := by
  rw [value12, value20, value23, value24, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(37 : Vertex), (49 : Vertex), (52 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (55 : Vertex) [(37 : Vertex), (49 : Vertex), (52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E121.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112121
