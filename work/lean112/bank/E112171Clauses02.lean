import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 22 = false ∨ valuation q 28 = false ∨ valuation q 37 = false := by
  rw [value22, value27, value28, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (149 : Vertex) (159 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 37 = false ∨ valuation q 97 = false := by
  rw [value24, value27, value37, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (157 : Vertex) (153 : Vertex) (221 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value23, value26, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (151 : Vertex) (155 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 14 = false ∨ valuation q 34 = false ∨ valuation q 40 = false := by
  rw [value14, value29, value34, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (214 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 143 = true ∨ valuation q 14 = true ∨ valuation q 40 = true := by
  rw [value14, value29, value40, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(134 : Vertex), (230 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (214 : Vertex) [(134 : Vertex), (230 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 144 = true ∨ valuation q 31 = true ∨ valuation q 41 = true := by
  rw [value30, value31, value41, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(201 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (136 : Vertex) [(201 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 144 = true ∨ valuation q 16 = true ∨ valuation q 41 = true := by
  rw [value16, value30, value41, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(136 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(136 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 144 = true ∨ valuation q 16 = true ∨ valuation q 31 = true := by
  rw [value16, value30, value31, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(136 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (232 : Vertex) [(136 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 17 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value17, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 30 = true ∨ valuation q 32 = true := by
  rw [value30, value31, value32, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(200 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (137 : Vertex) [(200 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 17 = true ∨ valuation q 32 = true := by
  rw [value17, value31, value32, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(137 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (200 : Vertex) [(137 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 17 = true ∨ valuation q 30 = true := by
  rw [value17, value30, value31, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(137 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (205 : Vertex) [(137 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 146 = true ∨ valuation q 33 = true ∨ valuation q 37 = true := by
  rw [value32, value33, value37, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (201 : Vertex) [(207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 146 = true ∨ valuation q 31 = true ∨ valuation q 33 = true := by
  rw [value31, value32, value33, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(201 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (221 : Vertex) [(201 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 147 = true := by
  rw [value33, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 34 = true := by
  rw [value34, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (214 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 148 = true ∨ valuation q 38 = true := by
  rw [value34, value38, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (198 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 148 = true ∨ valuation q 29 = true := by
  rw [value29, value34, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(198 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 149 = true ∨ valuation q 38 = true := by
  rw [value35, value38, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 149 = true ∨ valuation q 25 = true := by
  rw [value25, value35, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(154 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (222 : Vertex) [(154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 150 = true ∨ valuation q 38 = true := by
  rw [value36, value38, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 151 = true ∨ valuation q 27 = true ∨ valuation q 36 = true := by
  rw [value27, value36, value37, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(157 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (205 : Vertex) [(157 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value34, value35, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 152 = true ∨ valuation q 34 = true ∨ valuation q 35 = true := by
  rw [value34, value35, value38, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (220 : Vertex) [(214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 153 = true := by
  rw [value39, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (226 : Vertex) (230 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 29 = false ∨ valuation q 43 = false ∨ valuation q 101 = false := by
  rw [value29, value40, value43, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (198 : Vertex) (238 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 154 = true ∨ valuation q 29 = true ∨ valuation q 39 = true ∨ valuation q 43 = true := by
  rw [value29, value39, value40, value43, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(198 : Vertex), (226 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (486 : Vertex) [(198 : Vertex), (226 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 9 = false ∨ valuation q 30 = false ∨ valuation q 42 = false := by
  rw [value9, value30, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (200 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 9 = false ∨ valuation q 30 = false ∨ valuation q 103 = false := by
  rw [value9, value30, value41, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (200 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 9 = false ∨ valuation q 42 = false ∨ valuation q 103 = false := by
  rw [value9, value41, value42, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (104 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 30 = false ∨ valuation q 42 = false ∨ valuation q 103 = false := by
  rw [value30, value41, value42, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (200 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 156 = true ∨ valuation q 43 = true := by
  rw [value42, value43, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(238 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (232 : Vertex) [(238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E171.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112171
