import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 97 = false := by
  rw [value46, value48, value49, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (179 : Vertex) (182 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value46, value49, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (179 : Vertex) (191 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 97 = false := by
  rw [value46, value49, value56, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (179 : Vertex) (191 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 70 = false ∨ valuation q 97 = false := by
  rw [value46, value49, value70, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (179 : Vertex) (247 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value48, value49, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (182 : Vertex) (191 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 97 = false := by
  rw [value48, value49, value56, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (182 : Vertex) (191 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 48 = false ∨ valuation q 70 = false ∨ valuation q 97 = false := by
  rw [value48, value49, value70, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (182 : Vertex) (247 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 70 = false ∨ valuation q 97 = false := by
  rw [value49, value56, value70, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (191 : Vertex) (247 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 51 = false := by
  rw [value13, value44, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (176 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 52 = false := by
  rw [value13, value44, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (176 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 53 = false := by
  rw [value13, value44, value50, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (176 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 71 = false := by
  rw [value13, value44, value50, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (176 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 98 = false := by
  rw [value13, value44, value50, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (176 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value13, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (185 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 51 = false ∨ valuation q 53 = false := by
  rw [value13, value50, value51, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (185 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 51 = false ∨ valuation q 71 = false := by
  rw [value13, value50, value51, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (185 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 51 = false ∨ valuation q 98 = false := by
  rw [value13, value50, value51, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (185 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value13, value50, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (186 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 52 = false ∨ valuation q 71 = false := by
  rw [value13, value50, value52, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (186 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 52 = false ∨ valuation q 98 = false := by
  rw [value13, value50, value52, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (186 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 53 = false ∨ valuation q 71 = false := by
  rw [value13, value50, value53, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 53 = false ∨ valuation q 98 = false := by
  rw [value13, value50, value53, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 71 = false ∨ valuation q 98 = false := by
  rw [value13, value50, value71, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value44, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (185 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 53 = false := by
  rw [value44, value50, value51, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (185 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 71 = false := by
  rw [value44, value50, value51, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (185 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 98 = false := by
  rw [value44, value50, value51, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (185 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value44, value50, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (186 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 71 = false := by
  rw [value44, value50, value52, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (186 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 98 = false := by
  rw [value44, value50, value52, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (186 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 53 = false ∨ valuation q 71 = false := by
  rw [value44, value50, value53, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 53 = false ∨ valuation q 98 = false := by
  rw [value44, value50, value53, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E004.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112004
