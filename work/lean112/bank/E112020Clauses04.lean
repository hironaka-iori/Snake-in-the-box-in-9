import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value24, value25, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (112 : Vertex) (115 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 60 = false := by
  rw [value24, value25, value27, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (112 : Vertex) (115 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 29 = false ∨ valuation q 60 = false := by
  rw [value24, value25, value29, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (112 : Vertex) (121 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 60 = false := by
  rw [value25, value27, value29, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (115 : Vertex) (121 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 8 = true ∨ valuation q 15 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 60 = true := by
  rw [value8, value15, value25, value27, value29, value60, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (112 : Vertex) → w ∈ [(49 : Vertex), (97 : Vertex), (115 : Vertex), (121 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (112 : Vertex) [(49 : Vertex), (97 : Vertex), (115 : Vertex), (121 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value16, value24, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 30 = false := by
  rw [value16, value24, value26, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 61 = false := by
  rw [value16, value24, value26, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 78 = false := by
  rw [value16, value24, value26, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value16, value26, value27, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (115 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 61 = false := by
  rw [value16, value26, value27, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (115 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 78 = false := by
  rw [value16, value26, value27, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (115 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 61 = false := by
  rw [value16, value26, value30, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (122 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 78 = false := by
  rw [value16, value26, value30, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (122 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 16 = false ∨ valuation q 61 = false ∨ valuation q 78 = false := by
  rw [value16, value26, value61, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (242 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value24, value26, value27, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (115 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 61 = false := by
  rw [value24, value26, value27, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (115 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 78 = false := by
  rw [value24, value26, value27, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (115 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 61 = false := by
  rw [value24, value26, value30, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (122 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 78 = false := by
  rw [value24, value26, value30, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (122 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 61 = false ∨ valuation q 78 = false := by
  rw [value24, value26, value61, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (242 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 61 = false := by
  rw [value26, value27, value30, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (115 : Vertex) (122 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 78 = false := by
  rw [value26, value27, value30, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (115 : Vertex) (122 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 61 = false ∨ valuation q 78 = false := by
  rw [value26, value27, value61, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (115 : Vertex) (242 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 61 = false ∨ valuation q 78 = false := by
  rw [value26, value30, value61, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (122 : Vertex) (242 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 79 = false := by
  rw [value17, value25, value27, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (99 : Vertex) (113 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 62 = true ∨ valuation q 79 = true := by
  rw [value25, value26, value27, value62, value79, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(113 : Vertex), (114 : Vertex), (243 : Vertex), (371 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (99 : Vertex) [(113 : Vertex), (114 : Vertex), (243 : Vertex), (371 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 9 = false ∨ valuation q 24 = false ∨ valuation q 31 = false := by
  rw [value9, value24, value28, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (116 : Vertex) (52 : Vertex) (112 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 9 = false ∨ valuation q 24 = false ∨ valuation q 80 = false := by
  rw [value9, value24, value28, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (116 : Vertex) (52 : Vertex) (112 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 9 = false ∨ valuation q 31 = false ∨ valuation q 80 = false := by
  rw [value9, value28, value31, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (116 : Vertex) (52 : Vertex) (124 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 24 = false ∨ valuation q 31 = false ∨ valuation q 80 = false := by
  rw [value24, value28, value31, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (116 : Vertex) (112 : Vertex) (124 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value10, value19, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (57 : Vertex) (105 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E020.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112020
