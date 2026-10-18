import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 25 = false := by
  rw [value1, value13, value15, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 33 = false := by
  rw [value1, value13, value15, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 19 = false := by
  rw [value1, value14, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (162 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 25 = false := by
  rw [value1, value14, value15, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (162 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 33 = false := by
  rw [value1, value14, value15, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (162 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value1, value15, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value1, value15, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (171 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value1, value15, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (179 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 19 = false := by
  rw [value13, value14, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 25 = false := by
  rw [value13, value14, value15, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 33 = false := by
  rw [value13, value14, value15, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value13, value15, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value13, value15, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (171 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value13, value15, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (179 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value14, value15, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value14, value15, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (171 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value14, value15, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (179 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value15, value19, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (171 : Vertex) (179 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 20 = false := by
  rw [value3, value13, value16, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (37 : Vertex) (161 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 35 = false := by
  rw [value3, value13, value16, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (37 : Vertex) (161 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 85 = false := by
  rw [value3, value13, value16, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (37 : Vertex) (161 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 3 = false ∨ valuation q 20 = false ∨ valuation q 35 = false := by
  rw [value3, value16, value20, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (37 : Vertex) (173 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 35 = false := by
  rw [value13, value16, value20, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 85 = false := by
  rw [value13, value16, value20, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 13 = false ∨ valuation q 35 = false ∨ valuation q 85 = false := by
  rw [value13, value16, value35, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (229 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 35 = false ∨ valuation q 85 = false := by
  rw [value16, value20, value35, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (173 : Vertex) (229 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 14 = false ∨ valuation q 26 = false ∨ valuation q 36 = false := by
  rw [value14, value17, value26, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (182 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 14 = false ∨ valuation q 26 = false ∨ valuation q 86 = false := by
  rw [value14, value17, value26, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (182 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 14 = false ∨ valuation q 36 = false ∨ valuation q 86 = false := by
  rw [value14, value17, value36, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (230 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 36 = false ∨ valuation q 86 = false := by
  rw [value17, value26, value36, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (182 : Vertex) (230 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 138 = true ∨ valuation q 14 = true ∨ valuation q 36 = true ∨ valuation q 86 = true := by
  rw [value14, value17, value36, value86, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(162 : Vertex), (230 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (182 : Vertex) [(162 : Vertex), (230 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 12 = false ∨ valuation q 27 = false ∨ valuation q 88 = false := by
  rw [value12, value18, value27, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (184 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E024.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112024
