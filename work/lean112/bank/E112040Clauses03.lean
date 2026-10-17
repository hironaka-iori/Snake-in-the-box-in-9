import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 140 = true ∨ valuation q 22 = true ∨ valuation q 30 = true ∨ valuation q 92 = true := by
  rw [value20, value22, value30, value92, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (97 : Vertex) → w ∈ [(98 : Vertex), (112 : Vertex), (352 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (97 : Vertex) [(98 : Vertex), (112 : Vertex), (352 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 20 = true ∨ valuation q 23 = true ∨ valuation q 25 = true := by
  rw [value20, value21, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ∈ [(96 : Vertex), (99 : Vertex), (105 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (97 : Vertex) [(96 : Vertex), (99 : Vertex), (105 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 141 = true ∨ valuation q 23 = true ∨ valuation q 25 = true := by
  rw [value21, value23, value25, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(99 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (96 : Vertex) [(99 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 141 = true ∨ valuation q 20 = true ∨ valuation q 25 = true := by
  rw [value20, value21, value25, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(96 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (99 : Vertex) [(96 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 141 = true ∨ valuation q 20 = true ∨ valuation q 23 = true := by
  rw [value20, value21, value23, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(96 : Vertex), (99 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (105 : Vertex) [(96 : Vertex), (99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 142 = true ∨ valuation q 20 = true ∨ valuation q 23 = true ∨ valuation q 31 = true := by
  rw [value20, value22, value23, value31, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(96 : Vertex), (99 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (34 : Vertex) [(96 : Vertex), (99 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 142 = true ∨ valuation q 1 = true ∨ valuation q 23 = true ∨ valuation q 31 = true := by
  rw [value1, value22, value23, value31, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(34 : Vertex), (99 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (96 : Vertex) [(34 : Vertex), (99 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 142 = true ∨ valuation q 1 = true ∨ valuation q 20 = true ∨ valuation q 31 = true := by
  rw [value1, value20, value22, value31, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(34 : Vertex), (96 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (99 : Vertex) [(34 : Vertex), (96 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 142 = true ∨ valuation q 1 = true ∨ valuation q 20 = true ∨ valuation q 23 = true := by
  rw [value1, value20, value22, value23, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(34 : Vertex), (96 : Vertex), (99 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (114 : Vertex) [(34 : Vertex), (96 : Vertex), (99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value21, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (98 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 26 = false := by
  rw [value21, value22, value23, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (98 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 32 = false := by
  rw [value21, value22, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (98 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value21, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (103 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value21, value23, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (103 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value21, value23, value26, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (107 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value22, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (98 : Vertex) (103 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value22, value23, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (98 : Vertex) (103 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value22, value23, value26, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (98 : Vertex) (107 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 32 = false := by
  rw [value23, value24, value26, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (103 : Vertex) (107 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 144 = true ∨ valuation q 29 = true ∨ valuation q 35 = true ∨ valuation q 96 = true := by
  rw [value24, value29, value35, value96, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(111 : Vertex), (119 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (99 : Vertex) [(111 : Vertex), (119 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 144 = true ∨ valuation q 23 = true ∨ valuation q 35 = true ∨ valuation q 96 = true := by
  rw [value23, value24, value35, value96, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(99 : Vertex), (119 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (111 : Vertex) [(99 : Vertex), (119 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 144 = true ∨ valuation q 23 = true ∨ valuation q 29 = true ∨ valuation q 96 = true := by
  rw [value23, value24, value29, value96, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(99 : Vertex), (111 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (119 : Vertex) [(99 : Vertex), (111 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 144 = true ∨ valuation q 23 = true ∨ valuation q 29 = true ∨ valuation q 35 = true := by
  rw [value23, value24, value29, value35, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(99 : Vertex), (111 : Vertex), (119 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (359 : Vertex) [(99 : Vertex), (111 : Vertex), (119 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value6, value21, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (97 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 28 = false := by
  rw [value6, value21, value25, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (97 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 37 = false := by
  rw [value6, value21, value25, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (97 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 63 = false := by
  rw [value6, value21, value25, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (97 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 98 = false := by
  rw [value6, value21, value25, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (97 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value6, value25, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (107 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 37 = false := by
  rw [value6, value25, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (107 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 63 = false := by
  rw [value6, value25, value26, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (107 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 98 = false := by
  rw [value6, value25, value26, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (107 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E040.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112040
