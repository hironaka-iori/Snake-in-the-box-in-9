import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 139 = true ∨ valuation q 17 = true ∨ valuation q 20 = true := by
  rw [value17, value20, value22, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(22 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (31 : Vertex) [(22 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 21 = false := by
  rw [value11, value19, value21, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 22 = false := by
  rw [value11, value19, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 38 = false := by
  rw [value11, value19, value23, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 55 = false := by
  rw [value11, value19, value23, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 91 = false := by
  rw [value11, value19, value23, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value11, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 21 = false ∨ valuation q 38 = false := by
  rw [value11, value21, value23, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 21 = false ∨ valuation q 55 = false := by
  rw [value11, value21, value23, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 21 = false ∨ valuation q 91 = false := by
  rw [value11, value21, value23, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 22 = false ∨ valuation q 38 = false := by
  rw [value11, value22, value23, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (30 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 22 = false ∨ valuation q 55 = false := by
  rw [value11, value22, value23, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (30 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 22 = false ∨ valuation q 91 = false := by
  rw [value11, value22, value23, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (30 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 38 = false ∨ valuation q 55 = false := by
  rw [value11, value23, value38, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (95 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 38 = false ∨ valuation q 91 = false := by
  rw [value11, value23, value38, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (95 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 11 = false ∨ valuation q 55 = false ∨ valuation q 91 = false := by
  rw [value11, value23, value55, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (159 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value19, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (29 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 38 = false := by
  rw [value19, value21, value23, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (29 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 55 = false := by
  rw [value19, value21, value23, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (29 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 91 = false := by
  rw [value19, value21, value23, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (29 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 38 = false := by
  rw [value19, value22, value23, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (30 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 55 = false := by
  rw [value19, value22, value23, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (30 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 91 = false := by
  rw [value19, value22, value23, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (30 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 38 = false ∨ valuation q 55 = false := by
  rw [value19, value23, value38, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (95 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 38 = false ∨ valuation q 91 = false := by
  rw [value19, value23, value38, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (95 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 55 = false ∨ valuation q 91 = false := by
  rw [value19, value23, value55, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (159 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 38 = false := by
  rw [value21, value22, value23, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (30 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 55 = false := by
  rw [value21, value22, value23, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (30 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 91 = false := by
  rw [value21, value22, value23, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (30 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 38 = false ∨ valuation q 55 = false := by
  rw [value21, value23, value38, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (95 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 38 = false ∨ valuation q 91 = false := by
  rw [value21, value23, value38, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (95 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 55 = false ∨ valuation q 91 = false := by
  rw [value21, value23, value55, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (159 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E115.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112115
