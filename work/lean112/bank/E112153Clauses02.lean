import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value23, value24, value25, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(149 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (407 : Vertex) [(149 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 21 = true ∨ valuation q 27 = true := by
  rw [value21, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ∈ [(144 : Vertex), (154 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (152 : Vertex) [(144 : Vertex), (154 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value21, value27, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (152 : Vertex) (144 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 21 = true := by
  rw [value21, value26, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (154 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value17, value26, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (152 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value26, value27, value28, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(152 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (138 : Vertex) [(152 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 17 = true ∨ valuation q 28 = true := by
  rw [value17, value27, value28, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(138 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (152 : Vertex) [(138 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 17 = true ∨ valuation q 26 = true := by
  rw [value17, value26, value27, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (154 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(138 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (154 : Vertex) (155 : Vertex) [(138 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 43 = false := by
  rw [value18, value27, value28, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (139 : Vertex) (154 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 102 = false := by
  rw [value29, value30, value34, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 102 = false := by
  rw [value29, value31, value34, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (196 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 102 = true := by
  rw [value29, value31, value34, value102, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(196 : Vertex), (200 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (194 : Vertex) [(196 : Vertex), (200 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 30 = true ∨ valuation q 34 = true ∨ valuation q 102 = true := by
  rw [value29, value30, value34, value102, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(194 : Vertex), (200 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (196 : Vertex) [(194 : Vertex), (200 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 30 = true ∨ valuation q 31 = true ∨ valuation q 102 = true := by
  rw [value29, value30, value31, value102, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(194 : Vertex), (196 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(194 : Vertex), (196 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 39 = false := by
  rw [value29, value30, value32, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (192 : Vertex) (198 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 105 = false := by
  rw [value29, value31, value32, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (192 : Vertex) (198 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 14 = true ∨ valuation q 32 = true ∨ valuation q 105 = true := by
  rw [value14, value31, value32, value105, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(132 : Vertex), (198 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (192 : Vertex) [(132 : Vertex), (198 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value16, value30, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value30, value32, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (199 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 30 = true ∨ valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value30, value31, value32, value33, value36, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(194 : Vertex), (196 : Vertex), (199 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (134 : Vertex) [(194 : Vertex), (196 : Vertex), (199 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 16 = true ∨ valuation q 30 = true ∨ valuation q 31 = true ∨ valuation q 36 = true := by
  rw [value16, value30, value31, value32, value36, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(134 : Vertex), (194 : Vertex), (196 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (199 : Vertex) [(134 : Vertex), (194 : Vertex), (196 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 107 = false := by
  rw [value32, value33, value37, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (199 : Vertex) (198 : Vertex) (207 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 37 = true ∨ valuation q 107 = true := by
  rw [value33, value37, value107, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(207 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (198 : Vertex) [(207 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 107 = true := by
  rw [value32, value33, value107, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(198 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(198 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 29 = false ∨ valuation q 35 = false ∨ valuation q 108 = false := by
  rw [value29, value34, value35, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (201 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 29 = false ∨ valuation q 35 = false := by
  rw [value29, value35, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (200 : Vertex) (192 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 35 = true ∨ valuation q 108 = true := by
  rw [value34, value35, value108, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(201 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(201 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 29 = true ∨ valuation q 108 = true := by
  rw [value29, value34, value108, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(192 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(192 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 42 = true ∨ valuation q 109 = true := by
  rw [value35, value42, value109, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(217 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (200 : Vertex) [(217 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 34 = true ∨ valuation q 109 = true := by
  rw [value34, value35, value109, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(200 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (217 : Vertex) [(200 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 34 = true ∨ valuation q 42 = true := by
  rw [value34, value35, value42, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(200 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (457 : Vertex) [(200 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value32, value36, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (207 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E153.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112153
