import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 31 = false := by
  rw [value10, value19, value26, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (51 : Vertex) (99 : Vertex) (123 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 31 = false := by
  rw [value10, value25, value26, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (51 : Vertex) (114 : Vertex) (123 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 68 = false := by
  rw [value19, value25, value26, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (99 : Vertex) (114 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 32 = false := by
  rw [value24, value27, value28, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (116 : Vertex) (112 : Vertex) (118 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 147 = true ∨ valuation q 24 = true ∨ valuation q 32 = true := by
  rw [value24, value27, value32, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(112 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (118 : Vertex) [(112 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 147 = true ∨ valuation q 24 = true ∨ valuation q 28 = true := by
  rw [value24, value27, value28, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(112 : Vertex), (118 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (124 : Vertex) [(112 : Vertex), (118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 148 = true ∨ valuation q 27 = true := by
  rw [value27, value28, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(116 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (114 : Vertex) [(116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 148 = true ∨ valuation q 25 = true := by
  rw [value25, value28, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(114 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (116 : Vertex) [(114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value13, value21, value24, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (104 : Vertex) (112 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 30 = false := by
  rw [value13, value21, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (104 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 32 = false := by
  rw [value13, value21, value29, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (104 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 71 = false := by
  rw [value13, value21, value29, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (104 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 30 = false := by
  rw [value13, value24, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value13, value24, value29, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 71 = false := by
  rw [value13, value24, value29, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 82 = false := by
  rw [value13, value24, value29, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value13, value29, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (122 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 71 = false := by
  rw [value13, value29, value30, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (122 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 30 = false ∨ valuation q 82 = false := by
  rw [value13, value29, value30, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (122 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 32 = false ∨ valuation q 71 = false := by
  rw [value13, value29, value32, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (124 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 32 = false ∨ valuation q 82 = false := by
  rw [value13, value29, value32, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (124 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 13 = false ∨ valuation q 71 = false ∨ valuation q 82 = false := by
  rw [value13, value29, value71, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (248 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 30 = false := by
  rw [value21, value24, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (104 : Vertex) (112 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value21, value24, value29, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (104 : Vertex) (112 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 71 = false := by
  rw [value21, value24, value29, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (104 : Vertex) (112 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value21, value29, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (104 : Vertex) (122 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 71 = false := by
  rw [value21, value29, value30, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (104 : Vertex) (122 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = false ∨ valuation q 32 = false ∨ valuation q 71 = false := by
  rw [value21, value29, value32, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (104 : Vertex) (124 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 71 = false := by
  rw [value24, value29, value30, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (112 : Vertex) (122 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 30 = false ∨ valuation q 82 = false := by
  rw [value24, value29, value30, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (112 : Vertex) (122 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 71 = false ∨ valuation q 82 = false := by
  rw [value24, value29, value71, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (112 : Vertex) (248 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 71 = false := by
  rw [value29, value30, value32, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (122 : Vertex) (124 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E004.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112004
