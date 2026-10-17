import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 20 = false ∨ valuation q 67 = false := by
  rw [value11, value20, value30, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (96 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 20 = false ∨ valuation q 102 = false := by
  rw [value11, value20, value30, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (96 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value11, value30, value31, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (114 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 31 = false ∨ valuation q 67 = false := by
  rw [value11, value30, value31, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (114 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 31 = false ∨ valuation q 102 = false := by
  rw [value11, value30, value31, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (114 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 33 = false ∨ valuation q 67 = false := by
  rw [value11, value30, value33, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (116 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 33 = false ∨ valuation q 102 = false := by
  rw [value11, value30, value33, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (116 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 67 = false ∨ valuation q 102 = false := by
  rw [value11, value30, value67, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (240 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 31 = false ∨ valuation q 36 = false := by
  rw [value20, value30, value31, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (114 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 31 = false ∨ valuation q 67 = false := by
  rw [value20, value30, value31, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (114 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 31 = false ∨ valuation q 102 = false := by
  rw [value20, value30, value31, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (114 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value20, value30, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (116 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 33 = false ∨ valuation q 67 = false := by
  rw [value20, value30, value33, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (116 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 33 = false ∨ valuation q 102 = false := by
  rw [value20, value30, value33, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (116 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 67 = false ∨ valuation q 102 = false := by
  rw [value20, value30, value67, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (240 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value30, value31, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (114 : Vertex) (116 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 67 = false ∨ valuation q 102 = false := by
  rw [value30, value31, value67, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (114 : Vertex) (240 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 67 = false ∨ valuation q 102 = false := by
  rw [value30, value33, value67, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (116 : Vertex) (240 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value22, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 34 = false := by
  rw [value22, value30, value31, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 38 = false := by
  rw [value22, value30, value31, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 22 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value22, value31, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (115 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 22 = false ∨ valuation q 32 = false ∨ valuation q 38 = false := by
  rw [value22, value31, value32, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (115 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 22 = false ∨ valuation q 34 = false ∨ valuation q 38 = false := by
  rw [value22, value31, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value30, value31, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (115 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 38 = false := by
  rw [value30, value31, value32, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (115 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 38 = false := by
  rw [value30, value31, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 38 = false := by
  rw [value31, value32, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (115 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 68 = false := by
  rw [value13, value23, value32, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (51 : Vertex) (99 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 23 = false ∨ valuation q 31 = false ∨ valuation q 103 = false := by
  rw [value23, value31, value32, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (99 : Vertex) (114 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 152 = true ∨ valuation q 13 = true ∨ valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 68 = true ∨ valuation q 103 = true := by
  rw [value13, value31, value32, value35, value68, value103, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(51 : Vertex), (114 : Vertex), (119 : Vertex), (243 : Vertex), (371 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (99 : Vertex) [(51 : Vertex), (114 : Vertex), (119 : Vertex), (243 : Vertex), (371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 152 = true ∨ valuation q 13 = true ∨ valuation q 23 = true ∨ valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 103 = true := by
  rw [value13, value23, value31, value32, value35, value103, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(51 : Vertex), (99 : Vertex), (114 : Vertex), (119 : Vertex), (371 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (243 : Vertex) [(51 : Vertex), (99 : Vertex), (114 : Vertex), (119 : Vertex), (371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E040.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112040
