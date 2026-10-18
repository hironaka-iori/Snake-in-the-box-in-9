import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 32 = false ∨ valuation q 77 = false := by
  rw [value7, value22, value32, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (46 : Vertex) (126 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value20, value22, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (108 : Vertex) (111 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 23 = false ∨ valuation q 77 = false := by
  rw [value20, value22, value23, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (108 : Vertex) (111 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 32 = false ∨ valuation q 59 = false := by
  rw [value20, value22, value32, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (108 : Vertex) (126 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 32 = false ∨ valuation q 77 = false := by
  rw [value20, value22, value32, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (108 : Vertex) (126 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 59 = false ∨ valuation q 77 = false := by
  rw [value20, value22, value59, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (108 : Vertex) (238 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 59 = false := by
  rw [value22, value23, value32, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (111 : Vertex) (126 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 77 = false := by
  rw [value22, value23, value32, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (111 : Vertex) (126 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 59 = false ∨ valuation q 77 = false := by
  rw [value22, value23, value59, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (111 : Vertex) (238 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 32 = false ∨ valuation q 59 = false ∨ valuation q 77 = false := by
  rw [value22, value32, value59, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (126 : Vertex) (238 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value18, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (103 : Vertex) (109 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 21 = true ∨ valuation q 22 = true := by
  rw [value21, value22, value23, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(109 : Vertex), (110 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (103 : Vertex) [(109 : Vertex), (110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 18 = true ∨ valuation q 22 = true := by
  rw [value18, value22, value23, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(103 : Vertex), (110 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (109 : Vertex) [(103 : Vertex), (110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value14, value24, value25, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (113 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value24, value25, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (113 : Vertex) (114 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value24, value25, value26, value28, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (112 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(113 : Vertex), (114 : Vertex), (116 : Vertex)] := by decide
  have hg := other_cover q (112 : Vertex) (96 : Vertex) [(113 : Vertex), (114 : Vertex), (116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 14 = true ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value14, value24, value26, value28, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (112 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(96 : Vertex), (114 : Vertex), (116 : Vertex)] := by decide
  have hg := other_cover q (112 : Vertex) (113 : Vertex) [(96 : Vertex), (114 : Vertex), (116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 14 = true ∨ valuation q 25 = true ∨ valuation q 28 = true := by
  rw [value14, value24, value25, value28, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (112 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(96 : Vertex), (113 : Vertex), (116 : Vertex)] := by decide
  have hg := other_cover q (112 : Vertex) (114 : Vertex) [(96 : Vertex), (113 : Vertex), (116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 24 = false := by
  rw [value8, value15, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (97 : Vertex) (112 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 29 = false := by
  rw [value8, value15, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (97 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 15 = false ∨ valuation q 60 = false := by
  rw [value8, value15, value25, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (97 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value8, value24, value25, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (112 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 24 = false ∨ valuation q 29 = false := by
  rw [value8, value24, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (112 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 24 = false ∨ valuation q 60 = false := by
  rw [value8, value24, value25, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (112 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value8, value25, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (115 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 60 = false := by
  rw [value8, value25, value27, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (115 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = false ∨ valuation q 29 = false ∨ valuation q 60 = false := by
  rw [value8, value25, value29, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (121 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value15, value24, value25, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (97 : Vertex) (112 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 29 = false := by
  rw [value15, value24, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (97 : Vertex) (112 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 60 = false := by
  rw [value15, value24, value25, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (97 : Vertex) (112 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 27 = false ∨ valuation q 60 = false := by
  rw [value15, value25, value27, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (97 : Vertex) (115 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 29 = false ∨ valuation q 60 = false := by
  rw [value15, value25, value29, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (97 : Vertex) (121 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E020.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112020
