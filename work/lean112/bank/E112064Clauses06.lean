import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 161 = true ∨ valuation q 34 = true ∨ valuation q 40 = true ∨ valuation q 45 = true := by
  rw [value34, value40, value44, value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(204 : Vertex), (212 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (216 : Vertex) [(204 : Vertex), (212 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 41 = false := by
  rw [value16, value25, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (158 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 43 = false := by
  rw [value16, value25, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (158 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 44 = false := by
  rw [value16, value25, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (158 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 46 = false := by
  rw [value16, value25, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (158 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 116 = false := by
  rw [value16, value25, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (158 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value16, value41, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value16, value41, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (214 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 41 = false ∨ valuation q 46 = false := by
  rw [value16, value41, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (214 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 41 = false ∨ valuation q 116 = false := by
  rw [value16, value41, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (214 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value16, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 43 = false ∨ valuation q 116 = false := by
  rw [value16, value43, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (218 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 44 = false ∨ valuation q 116 = false := by
  rw [value16, value44, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (220 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 16 = false ∨ valuation q 46 = false ∨ valuation q 116 = false := by
  rw [value16, value45, value46, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (94 : Vertex) (223 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value25, value41, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value25, value41, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (214 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 41 = false ∨ valuation q 46 = false := by
  rw [value25, value41, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (214 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 41 = false ∨ valuation q 116 = false := by
  rw [value25, value41, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (214 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value25, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value25, value43, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (218 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 116 = false := by
  rw [value25, value43, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (218 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value25, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (220 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 44 = false ∨ valuation q 116 = false := by
  rw [value25, value44, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (220 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 46 = false ∨ valuation q 116 = false := by
  rw [value25, value45, value46, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (158 : Vertex) (223 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value41, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value41, value43, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 116 = false := by
  rw [value41, value43, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value41, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (220 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 116 = false := by
  rw [value41, value44, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (220 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 46 = false ∨ valuation q 116 = false := by
  rw [value41, value45, value46, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (223 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value43, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (218 : Vertex) (220 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 116 = false := by
  rw [value43, value44, value45, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (218 : Vertex) (220 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E064.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112064
