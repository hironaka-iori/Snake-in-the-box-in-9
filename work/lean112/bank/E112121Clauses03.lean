import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 35 = false := by
  rw [value3, value10, value13, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (34 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 47 = false := by
  rw [value3, value10, value13, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (34 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 71 = false := by
  rw [value3, value10, value13, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (34 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 14 = false := by
  rw [value3, value11, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (39 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 19 = false := by
  rw [value3, value11, value13, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 25 = false := by
  rw [value3, value11, value13, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 35 = false := by
  rw [value3, value11, value13, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 47 = false := by
  rw [value3, value11, value13, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 71 = false := by
  rw [value3, value11, value13, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 19 = false := by
  rw [value3, value13, value14, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (39 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 25 = false := by
  rw [value3, value13, value14, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (39 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 35 = false := by
  rw [value3, value13, value14, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (39 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 47 = false := by
  rw [value3, value13, value14, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (39 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 14 = false ∨ valuation q 71 = false := by
  rw [value3, value13, value14, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (39 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value3, value13, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (46 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 19 = false ∨ valuation q 35 = false := by
  rw [value3, value13, value19, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (46 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 19 = false ∨ valuation q 47 = false := by
  rw [value3, value13, value19, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (46 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 19 = false ∨ valuation q 71 = false := by
  rw [value3, value13, value19, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (46 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 25 = false ∨ valuation q 35 = false := by
  rw [value3, value13, value25, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (54 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 25 = false ∨ valuation q 47 = false := by
  rw [value3, value13, value25, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (54 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 25 = false ∨ valuation q 71 = false := by
  rw [value3, value13, value25, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (54 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value3, value13, value35, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (102 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 35 = false ∨ valuation q 71 = false := by
  rw [value3, value13, value35, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (102 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 3 = false ∨ valuation q 47 = false ∨ valuation q 71 = false := by
  rw [value3, value13, value47, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (166 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 14 = false := by
  rw [value10, value11, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (36 : Vertex) (39 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 19 = false := by
  rw [value10, value11, value13, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (36 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 25 = false := by
  rw [value10, value11, value13, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (36 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 35 = false := by
  rw [value10, value11, value13, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (36 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 47 = false := by
  rw [value10, value11, value13, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (36 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 71 = false := by
  rw [value10, value11, value13, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (36 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 14 = false ∨ valuation q 19 = false := by
  rw [value10, value13, value14, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (39 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 14 = false ∨ valuation q 25 = false := by
  rw [value10, value13, value14, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (34 : Vertex) (39 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E121.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112121
