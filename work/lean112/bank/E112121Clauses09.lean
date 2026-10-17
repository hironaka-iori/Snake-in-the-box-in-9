import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 23 = false := by
  rw [value7, value13, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (38 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 26 = false := by
  rw [value7, value13, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (38 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 56 = false := by
  rw [value7, value13, value25, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (38 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value7, value21, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (50 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value7, value21, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (50 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 30 = false := by
  rw [value7, value21, value25, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (50 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 56 = false := by
  rw [value7, value21, value25, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (50 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value7, value23, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (52 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 30 = false := by
  rw [value7, value23, value25, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (52 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 39 = false := by
  rw [value7, value23, value25, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (52 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 56 = false := by
  rw [value7, value23, value25, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (52 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 30 = false := by
  rw [value7, value25, value26, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (55 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 56 = false := by
  rw [value7, value25, value26, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (55 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 30 = false ∨ valuation q 39 = false := by
  rw [value7, value25, value30, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (62 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 30 = false ∨ valuation q 56 = false := by
  rw [value7, value25, value30, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (62 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 30 = false ∨ valuation q 82 = false := by
  rw [value7, value25, value30, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (22 : Vertex) (62 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value13, value21, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (38 : Vertex) (50 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value13, value21, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (38 : Vertex) (50 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 30 = false := by
  rw [value13, value21, value25, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (38 : Vertex) (50 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 56 = false := by
  rw [value13, value21, value25, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (38 : Vertex) (50 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 56 = false := by
  rw [value13, value23, value25, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (38 : Vertex) (52 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 13 = false ∨ valuation q 26 = false ∨ valuation q 56 = false := by
  rw [value13, value25, value26, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (38 : Vertex) (55 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value21, value23, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (50 : Vertex) (52 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 30 = false := by
  rw [value21, value23, value25, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (50 : Vertex) (52 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 56 = false := by
  rw [value21, value23, value25, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (50 : Vertex) (52 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 30 = false := by
  rw [value21, value25, value26, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (50 : Vertex) (55 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 56 = false := by
  rw [value21, value25, value26, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (50 : Vertex) (55 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 56 = false := by
  rw [value21, value25, value30, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (50 : Vertex) (62 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 82 = false := by
  rw [value21, value25, value30, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (50 : Vertex) (62 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 30 = false ∨ valuation q 56 = false := by
  rw [value23, value25, value30, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (52 : Vertex) (62 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 30 = false ∨ valuation q 82 = false := by
  rw [value23, value25, value30, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (52 : Vertex) (62 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 39 = false ∨ valuation q 56 = false := by
  rw [value23, value25, value39, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (54 : Vertex) (52 : Vertex) (118 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E121.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112121
