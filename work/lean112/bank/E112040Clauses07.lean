import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 152 = true ∨ valuation q 13 = true ∨ valuation q 23 = true ∨ valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 68 = true := by
  rw [value13, value23, value31, value32, value35, value68, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(51 : Vertex), (99 : Vertex), (114 : Vertex), (119 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (371 : Vertex) [(51 : Vertex), (99 : Vertex), (114 : Vertex), (119 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 39 = false := by
  rw [value30, value33, value34, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (116 : Vertex) (112 : Vertex) (118 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 154 = true ∨ valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 41 = true := by
  rw [value33, value34, value35, value41, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(116 : Vertex), (119 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (114 : Vertex) [(116 : Vertex), (119 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 154 = true ∨ valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 41 = true := by
  rw [value31, value34, value35, value41, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(114 : Vertex), (119 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (116 : Vertex) [(114 : Vertex), (119 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 154 = true ∨ valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 41 = true := by
  rw [value31, value33, value34, value41, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(114 : Vertex), (116 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (119 : Vertex) [(114 : Vertex), (116 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 154 = true ∨ valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 35 = true := by
  rw [value31, value33, value34, value35, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(114 : Vertex), (116 : Vertex), (119 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (126 : Vertex) [(114 : Vertex), (116 : Vertex), (119 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value15, value24, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (103 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 34 = false := by
  rw [value15, value24, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (103 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 42 = false := by
  rw [value15, value24, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (103 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 70 = false := by
  rw [value15, value24, value35, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (103 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 105 = false := by
  rw [value15, value24, value35, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (103 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value15, value32, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (115 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 32 = false ∨ valuation q 70 = false := by
  rw [value15, value32, value35, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (115 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 32 = false ∨ valuation q 105 = false := by
  rw [value15, value32, value35, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (115 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 34 = false ∨ valuation q 70 = false := by
  rw [value15, value34, value35, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (118 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 15 = false ∨ valuation q 70 = false ∨ valuation q 105 = false := by
  rw [value15, value35, value70, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (55 : Vertex) (247 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value24, value32, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (103 : Vertex) (115 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 42 = false := by
  rw [value24, value32, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (103 : Vertex) (115 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 70 = false := by
  rw [value24, value32, value35, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (103 : Vertex) (115 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 105 = false := by
  rw [value24, value32, value35, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (103 : Vertex) (115 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 24 = false ∨ valuation q 34 = false ∨ valuation q 42 = false := by
  rw [value24, value34, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (103 : Vertex) (118 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 24 = false ∨ valuation q 34 = false ∨ valuation q 70 = false := by
  rw [value24, value34, value35, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (103 : Vertex) (118 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 24 = false ∨ valuation q 42 = false ∨ valuation q 70 = false := by
  rw [value24, value35, value42, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (103 : Vertex) (127 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 24 = false ∨ valuation q 70 = false ∨ valuation q 105 = false := by
  rw [value24, value35, value70, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (103 : Vertex) (247 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 42 = false := by
  rw [value32, value34, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (115 : Vertex) (118 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 70 = false := by
  rw [value32, value34, value35, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (115 : Vertex) (118 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 105 = false := by
  rw [value32, value34, value35, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (115 : Vertex) (118 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 70 = false ∨ valuation q 105 = false := by
  rw [value32, value35, value70, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (115 : Vertex) (247 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 37 = false := by
  rw [value16, value30, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 38 = false := by
  rw [value16, value30, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 39 = false := by
  rw [value16, value30, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 71 = false := by
  rw [value16, value30, value36, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E040.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112040
