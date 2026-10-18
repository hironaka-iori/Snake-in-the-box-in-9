import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 27 = false := by
  rw [value8, value10, value15, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 45 = false := by
  rw [value8, value10, value15, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 69 = false := by
  rw [value8, value10, value15, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (271 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 19 = false ∨ valuation q 27 = false := by
  rw [value8, value10, value19, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (279 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 19 = false ∨ valuation q 45 = false := by
  rw [value8, value10, value19, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 19 = false ∨ valuation q 69 = false := by
  rw [value8, value10, value19, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 45 = false := by
  rw [value8, value10, value27, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (295 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 69 = false := by
  rw [value8, value10, value27, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (295 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value8, value10, value45, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value9, value10, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 27 = false := by
  rw [value9, value10, value15, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 45 = false := by
  rw [value9, value10, value15, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 69 = false := by
  rw [value9, value10, value15, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 19 = false ∨ valuation q 27 = false := by
  rw [value9, value10, value19, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 19 = false ∨ valuation q 45 = false := by
  rw [value9, value10, value19, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 19 = false ∨ valuation q 69 = false := by
  rw [value9, value10, value19, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 27 = false ∨ valuation q 45 = false := by
  rw [value9, value10, value27, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (295 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 27 = false ∨ valuation q 69 = false := by
  rw [value9, value10, value27, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (295 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value9, value10, value45, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 27 = false := by
  rw [value10, value15, value19, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 45 = false := by
  rw [value10, value15, value19, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 69 = false := by
  rw [value10, value15, value19, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 27 = false ∨ valuation q 45 = false := by
  rw [value10, value15, value27, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (295 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 27 = false ∨ valuation q 69 = false := by
  rw [value10, value15, value27, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (295 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value10, value15, value45, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 27 = false ∨ valuation q 45 = false := by
  rw [value10, value19, value27, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (279 : Vertex) (295 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 27 = false ∨ valuation q 69 = false := by
  rw [value10, value19, value27, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (279 : Vertex) (295 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value10, value19, value45, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (279 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 27 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value10, value27, value45, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (295 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 132 = true ∨ valuation q 9 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 69 = true := by
  rw [value9, value10, value15, value19, value27, value45, value69, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(262 : Vertex), (271 : Vertex), (279 : Vertex), (295 : Vertex), (327 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (261 : Vertex) [(262 : Vertex), (271 : Vertex), (279 : Vertex), (295 : Vertex), (327 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 132 = true ∨ valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 19 = true ∨ valuation q 27 = true ∨ valuation q 45 = true ∨ valuation q 69 = true := by
  rw [value8, value9, value10, value19, value27, value45, value69, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (279 : Vertex), (295 : Vertex), (327 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (271 : Vertex) [(261 : Vertex), (262 : Vertex), (279 : Vertex), (295 : Vertex), (327 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 70 = false := by
  rw [value11, value12, value14, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (265 : Vertex) (268 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E254.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112254
