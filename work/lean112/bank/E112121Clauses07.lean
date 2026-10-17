import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 24 = false ∨ valuation q 53 = false := by
  rw [value9, value20, value24, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (53 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 24 = false ∨ valuation q 78 = false := by
  rw [value9, value20, value24, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (53 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 27 = false ∨ valuation q 53 = false := by
  rw [value9, value20, value27, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (57 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 27 = false ∨ valuation q 78 = false := by
  rw [value9, value20, value27, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (57 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 53 = false ∨ valuation q 78 = false := by
  rw [value9, value20, value53, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (33 : Vertex) (177 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value20, value22, value24, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (51 : Vertex) (53 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 53 = false := by
  rw [value20, value22, value24, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (51 : Vertex) (53 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 78 = false := by
  rw [value20, value22, value24, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (51 : Vertex) (53 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 53 = false := by
  rw [value20, value22, value27, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (51 : Vertex) (57 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 78 = false := by
  rw [value20, value22, value27, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (51 : Vertex) (57 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 53 = false ∨ valuation q 78 = false := by
  rw [value20, value22, value53, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (51 : Vertex) (177 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 53 = false := by
  rw [value20, value24, value27, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (53 : Vertex) (57 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 78 = false := by
  rw [value20, value24, value27, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (53 : Vertex) (57 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 53 = false ∨ valuation q 78 = false := by
  rw [value20, value24, value53, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (53 : Vertex) (177 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 27 = false ∨ valuation q 53 = false ∨ valuation q 78 = false := by
  rw [value20, value27, value53, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (57 : Vertex) (177 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 22 = false := by
  rw [value5, value10, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (34 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 25 = false := by
  rw [value5, value10, value21, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (34 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 28 = false := by
  rw [value5, value10, value21, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (34 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 54 = false := by
  rw [value5, value10, value21, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (34 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 79 = false := by
  rw [value5, value10, value21, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (34 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 22 = false ∨ valuation q 28 = false := by
  rw [value5, value21, value22, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (51 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 22 = false ∨ valuation q 54 = false := by
  rw [value5, value21, value22, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (51 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 22 = false ∨ valuation q 79 = false := by
  rw [value5, value21, value22, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (51 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value5, value21, value25, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (54 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 25 = false ∨ valuation q 54 = false := by
  rw [value5, value21, value25, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (54 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 25 = false ∨ valuation q 79 = false := by
  rw [value5, value21, value25, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (54 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 28 = false ∨ valuation q 54 = false := by
  rw [value5, value21, value28, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (58 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 28 = false ∨ valuation q 79 = false := by
  rw [value5, value21, value28, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (58 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 54 = false ∨ valuation q 79 = false := by
  rw [value5, value21, value54, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (178 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value10, value21, value22, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (51 : Vertex) (54 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 22 = false ∨ valuation q 28 = false := by
  rw [value10, value21, value22, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (51 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 10 = false ∨ valuation q 22 = false ∨ valuation q 54 = false := by
  rw [value10, value21, value22, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (34 : Vertex) (51 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E121.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112121
