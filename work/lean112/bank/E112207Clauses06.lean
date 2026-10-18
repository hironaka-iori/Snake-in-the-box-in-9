import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value1, value45, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 85 = false := by
  rw [value45, value46, value47, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (257 : Vertex) (258 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value45, value46, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (257 : Vertex) (260 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 68 = false := by
  rw [value45, value46, value48, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (257 : Vertex) (260 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 85 = false := by
  rw [value45, value46, value48, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (257 : Vertex) (260 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value45, value46, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (257 : Vertex) (264 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value45, value46, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (257 : Vertex) (264 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value45, value46, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (257 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value45, value47, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (258 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value45, value48, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (260 : Vertex) (264 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value45, value48, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (260 : Vertex) (264 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 48 = false ∨ valuation q 68 = false ∨ valuation q 85 = false := by
  rw [value45, value48, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (260 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 162 = true ∨ valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 68 = true ∨ valuation q 85 = true := by
  rw [value45, value46, value47, value48, value52, value68, value85, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (256 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(257 : Vertex), (258 : Vertex), (260 : Vertex), (264 : Vertex), (320 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (256 : Vertex) (0 : Vertex) [(257 : Vertex), (258 : Vertex), (260 : Vertex), (264 : Vertex), (320 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 162 = true ∨ valuation q 1 = true ∨ valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 85 = true := by
  rw [value1, value45, value46, value47, value48, value52, value85, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (256 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(0 : Vertex), (257 : Vertex), (258 : Vertex), (260 : Vertex), (264 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (256 : Vertex) (320 : Vertex) [(0 : Vertex), (257 : Vertex), (258 : Vertex), (260 : Vertex), (264 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 162 = true ∨ valuation q 1 = true ∨ valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 68 = true := by
  rw [value1, value45, value46, value47, value48, value52, value68, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (256 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(0 : Vertex), (257 : Vertex), (258 : Vertex), (260 : Vertex), (264 : Vertex), (320 : Vertex)] := by decide
  have hg := other_cover q (256 : Vertex) (384 : Vertex) [(0 : Vertex), (257 : Vertex), (258 : Vertex), (260 : Vertex), (264 : Vertex), (320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 45 = false ∨ valuation q 49 = false := by
  rw [value2, value45, value46, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (256 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 45 = false ∨ valuation q 58 = false := by
  rw [value2, value45, value46, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (256 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value2, value45, value46, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (256 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 45 = false ∨ valuation q 86 = false := by
  rw [value2, value45, value46, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (256 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 49 = false ∨ valuation q 58 = false := by
  rw [value2, value46, value49, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (261 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 49 = false ∨ valuation q 69 = false := by
  rw [value2, value46, value49, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (261 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 49 = false ∨ valuation q 86 = false := by
  rw [value2, value46, value49, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (261 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 58 = false ∨ valuation q 69 = false := by
  rw [value2, value46, value58, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (273 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 58 = false ∨ valuation q 86 = false := by
  rw [value2, value46, value58, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (273 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 69 = false ∨ valuation q 86 = false := by
  rw [value2, value46, value69, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 58 = false := by
  rw [value45, value46, value49, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (256 : Vertex) (261 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 86 = false := by
  rw [value45, value46, value49, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (256 : Vertex) (261 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 58 = false ∨ valuation q 69 = false := by
  rw [value45, value46, value58, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (256 : Vertex) (273 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 69 = false ∨ valuation q 86 = false := by
  rw [value45, value46, value69, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (256 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 58 = false ∨ valuation q 69 = false := by
  rw [value46, value49, value58, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (261 : Vertex) (273 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 69 = false ∨ valuation q 86 = false := by
  rw [value46, value49, value69, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (261 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 58 = false ∨ valuation q 69 = false ∨ valuation q 86 = false := by
  rw [value46, value58, value69, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (273 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E207.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112207
