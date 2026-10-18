import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value5, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (171 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 40 = false ∨ valuation q 51 = false := by
  rw [value5, value39, value40, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (171 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 40 = false ∨ valuation q 61 = false := by
  rw [value5, value39, value40, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (171 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 40 = false ∨ valuation q 90 = false := by
  rw [value5, value39, value40, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (171 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 42 = false ∨ valuation q 51 = false := by
  rw [value5, value39, value42, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (173 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 42 = false ∨ valuation q 61 = false := by
  rw [value5, value39, value42, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (173 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 42 = false ∨ valuation q 90 = false := by
  rw [value5, value39, value42, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (173 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 61 = false := by
  rw [value5, value39, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 90 = false := by
  rw [value5, value39, value51, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 61 = false ∨ valuation q 90 = false := by
  rw [value5, value39, value61, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value35, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (171 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 51 = false := by
  rw [value35, value39, value40, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (171 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 61 = false := by
  rw [value35, value39, value40, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (171 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 51 = false := by
  rw [value35, value39, value42, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (173 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 61 = false := by
  rw [value35, value39, value42, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (173 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 90 = false := by
  rw [value35, value39, value42, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (173 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 51 = false ∨ valuation q 61 = false := by
  rw [value35, value39, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 51 = false ∨ valuation q 90 = false := by
  rw [value35, value39, value51, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 35 = false ∨ valuation q 61 = false ∨ valuation q 90 = false := by
  rw [value35, value39, value61, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 51 = false := by
  rw [value39, value40, value42, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (173 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 61 = false := by
  rw [value39, value40, value42, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (173 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 90 = false := by
  rw [value39, value40, value42, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (173 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 51 = false ∨ valuation q 61 = false := by
  rw [value39, value40, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 51 = false ∨ valuation q 90 = false := by
  rw [value39, value40, value51, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 61 = false ∨ valuation q 90 = false := by
  rw [value39, value40, value61, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 61 = false := by
  rw [value39, value42, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (173 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 90 = false := by
  rw [value39, value42, value51, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (173 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 61 = false ∨ valuation q 90 = false := by
  rw [value39, value42, value61, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (173 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 90 = false := by
  rw [value39, value51, value61, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (185 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 7 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value7, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (43 : Vertex) (163 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 7 = false ∨ valuation q 37 = false ∨ valuation q 43 = false := by
  rw [value7, value37, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (43 : Vertex) (163 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 7 = false ∨ valuation q 37 = false ∨ valuation q 63 = false := by
  rw [value7, value37, value40, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (43 : Vertex) (163 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E004.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112004
