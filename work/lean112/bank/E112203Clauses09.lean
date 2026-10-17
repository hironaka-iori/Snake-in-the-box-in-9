import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value53, value55, value56, value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(266 : Vertex), (268 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (262 : Vertex) [(266 : Vertex), (268 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value50, value55, value56, value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(262 : Vertex), (268 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (266 : Vertex) [(262 : Vertex), (268 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 57 = true := by
  rw [value50, value53, value56, value57, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(262 : Vertex), (266 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (268 : Vertex) [(262 : Vertex), (266 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 173 = true ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 55 = true := by
  rw [value50, value53, value55, value56, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(262 : Vertex), (266 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (271 : Vertex) [(262 : Vertex), (266 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value7, value51, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value7, value51, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 51 = false ∨ valuation q 67 = false := by
  rw [value7, value51, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 51 = false ∨ valuation q 76 = false := by
  rw [value7, value51, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 51 = false ∨ valuation q 94 = false := by
  rw [value7, value51, value57, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (263 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value7, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 67 = false := by
  rw [value7, value54, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 76 = false := by
  rw [value7, value54, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 94 = false := by
  rw [value7, value54, value57, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (267 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 56 = false ∨ valuation q 67 = false := by
  rw [value7, value56, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (270 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 56 = false ∨ valuation q 76 = false := by
  rw [value7, value56, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (270 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 56 = false ∨ valuation q 94 = false := by
  rw [value7, value56, value57, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (270 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 67 = false ∨ valuation q 76 = false := by
  rw [value7, value57, value67, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 67 = false ∨ valuation q 94 = false := by
  rw [value7, value57, value67, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (287 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 7 = false ∨ valuation q 76 = false ∨ valuation q 94 = false := by
  rw [value7, value57, value76, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (15 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value51, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 67 = false := by
  rw [value51, value54, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 76 = false := by
  rw [value51, value54, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 94 = false := by
  rw [value51, value54, value57, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 67 = false := by
  rw [value51, value56, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (270 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 76 = false := by
  rw [value51, value56, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (270 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 94 = false := by
  rw [value51, value56, value57, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (270 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 76 = false := by
  rw [value51, value57, value67, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 94 = false := by
  rw [value51, value57, value67, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (287 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 67 = false := by
  rw [value54, value56, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (270 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 76 = false := by
  rw [value54, value56, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (270 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 94 = false := by
  rw [value54, value56, value57, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (270 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 67 = false ∨ valuation q 76 = false := by
  rw [value54, value57, value67, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (287 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E203.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112203
