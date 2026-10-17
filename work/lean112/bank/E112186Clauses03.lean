import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 1 = false ∨ valuation q 31 = false ∨ valuation q 37 = false := by
  rw [value1, value31, value32, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 1 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value1, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (69 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 15 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value15, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (193 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 15 = false ∨ valuation q 31 = false ∨ valuation q 37 = false := by
  rw [value15, value31, value32, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 15 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value15, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value31, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 38 = false ∨ valuation q 110 = false := by
  rw [value32, value33, value38, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (197 : Vertex) (207 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 38 = true ∨ valuation q 110 = true := by
  rw [value33, value38, value110, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(207 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (197 : Vertex) [(207 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 110 = true := by
  rw [value32, value33, value110, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(197 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(197 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value32, value33, value38, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(197 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (455 : Vertex) [(197 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 2 = false ∨ valuation q 30 = false ∨ valuation q 111 = false := by
  rw [value2, value30, value34, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (72 : Vertex) (192 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 30 = true ∨ valuation q 35 = true ∨ valuation q 111 = true := by
  rw [value30, value34, value35, value111, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(192 : Vertex), (201 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (72 : Vertex) [(192 : Vertex), (201 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 2 = true ∨ valuation q 35 = true ∨ valuation q 111 = true := by
  rw [value2, value34, value35, value111, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(72 : Vertex), (201 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(72 : Vertex), (201 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 2 = true ∨ valuation q 30 = true ∨ valuation q 35 = true := by
  rw [value2, value30, value34, value35, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(72 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (456 : Vertex) [(72 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 31 = false ∨ valuation q 34 = false := by
  rw [value16, value31, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 31 = false ∨ valuation q 37 = false := by
  rw [value16, value31, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value16, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value16, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 34 = false ∨ valuation q 112 = false := by
  rw [value16, value34, value35, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 36 = false ∨ valuation q 112 = false := by
  rw [value16, value35, value36, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (203 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 16 = false ∨ valuation q 37 = false ∨ valuation q 112 = false := by
  rw [value16, value35, value37, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value31, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value31, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 112 = false := by
  rw [value31, value34, value35, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value31, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 112 = false := by
  rw [value31, value35, value36, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (203 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 31 = false ∨ valuation q 37 = false ∨ valuation q 112 = false := by
  rw [value31, value35, value37, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value34, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (203 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 112 = false := by
  rw [value34, value35, value36, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (203 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 112 = false := by
  rw [value34, value35, value37, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 112 = false := by
  rw [value35, value36, value37, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (203 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 4 = false ∨ valuation q 18 = false ∨ valuation q 38 = false := by
  rw [value4, value18, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (139 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E186.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112186
