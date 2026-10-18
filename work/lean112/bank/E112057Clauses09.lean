import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 39 = false ∨ valuation q 47 = false := by
  rw [value4, value39, value40, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (132 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 39 = false ∨ valuation q 50 = false := by
  rw [value4, value39, value40, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (132 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 39 = false ∨ valuation q 59 = false := by
  rw [value4, value39, value40, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (132 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 39 = false ∨ valuation q 112 = false := by
  rw [value4, value39, value40, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (132 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 42 = false ∨ valuation q 47 = false := by
  rw [value4, value40, value42, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (135 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 42 = false ∨ valuation q 50 = false := by
  rw [value4, value40, value42, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (135 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 42 = false ∨ valuation q 59 = false := by
  rw [value4, value40, value42, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (135 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 42 = false ∨ valuation q 112 = false := by
  rw [value4, value40, value42, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (135 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value4, value40, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value4, value40, value47, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (141 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 47 = false ∨ valuation q 112 = false := by
  rw [value4, value40, value47, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (141 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value4, value40, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (149 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 50 = false ∨ valuation q 112 = false := by
  rw [value4, value40, value50, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (149 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 59 = false ∨ valuation q 112 = false := by
  rw [value4, value40, value59, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (5 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 47 = false := by
  rw [value39, value40, value42, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 50 = false := by
  rw [value39, value40, value42, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 59 = false := by
  rw [value39, value40, value42, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 112 = false := by
  rw [value39, value40, value42, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (135 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value39, value40, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value39, value40, value47, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (141 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value39, value40, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (149 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 50 = false ∨ valuation q 112 = false := by
  rw [value39, value40, value50, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (149 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 59 = false ∨ valuation q 112 = false := by
  rw [value39, value40, value59, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value40, value42, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value40, value42, value47, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (141 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value40, value42, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (149 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 50 = false ∨ valuation q 112 = false := by
  rw [value40, value42, value50, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (149 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 59 = false ∨ valuation q 112 = false := by
  rw [value40, value42, value59, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (135 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value40, value47, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (141 : Vertex) (149 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 47 = false ∨ valuation q 59 = false ∨ valuation q 112 = false := by
  rw [value40, value47, value59, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (141 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 50 = false ∨ valuation q 59 = false ∨ valuation q 112 = false := by
  rw [value40, value50, value59, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (149 : Vertex) (197 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 167 = true ∨ valuation q 4 = true ∨ valuation q 42 = true ∨ valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 59 = true ∨ valuation q 112 = true := by
  rw [value4, value40, value42, value47, value50, value59, value112, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(5 : Vertex), (135 : Vertex), (141 : Vertex), (149 : Vertex), (197 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (132 : Vertex) [(5 : Vertex), (135 : Vertex), (141 : Vertex), (149 : Vertex), (197 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E057.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112057
