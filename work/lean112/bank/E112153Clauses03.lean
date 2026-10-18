import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 113 = false := by
  rw [value32, value36, value37, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (207 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 32 = false ∨ valuation q 46 = false ∨ valuation q 113 = false := by
  rw [value32, value36, value46, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 113 = false := by
  rw [value36, value37, value46, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (207 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 160 = true ∨ valuation q 32 = true ∨ valuation q 46 = true ∨ valuation q 113 = true := by
  rw [value32, value36, value46, value113, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(198 : Vertex), (222 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (207 : Vertex) [(198 : Vertex), (222 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 160 = true ∨ valuation q 32 = true ∨ valuation q 37 = true ∨ valuation q 113 = true := by
  rw [value32, value36, value37, value113, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(198 : Vertex), (207 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (222 : Vertex) [(198 : Vertex), (207 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 114 = true := by
  rw [value36, value37, value114, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(206 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(206 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 33 = true ∨ valuation q 114 = true := by
  rw [value33, value37, value114, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(199 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (206 : Vertex) [(199 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value33, value36, value37, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(199 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (463 : Vertex) [(199 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 41 = true ∨ valuation q 42 = true := by
  rw [value38, value41, value42, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(213 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (211 : Vertex) [(213 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value38, value40, value41, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(211 : Vertex), (213 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (217 : Vertex) [(211 : Vertex), (213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(211 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (194 : Vertex) [(211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 30 = true := by
  rw [value30, value39, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(194 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (211 : Vertex) [(194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 40 = true := by
  rw [value40, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (211 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 43 = true := by
  rw [value38, value39, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ∈ [(209 : Vertex), (210 : Vertex), (219 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (211 : Vertex) [(209 : Vertex), (210 : Vertex), (219 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value38, value39, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (209 : Vertex) (210 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 164 = true ∨ valuation q 38 = true ∨ valuation q 43 = true := by
  rw [value38, value40, value43, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(209 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (210 : Vertex) [(209 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 164 = true ∨ valuation q 38 = true ∨ valuation q 39 = true := by
  rw [value38, value39, value40, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(209 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (219 : Vertex) [(209 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 23 = false ∨ valuation q 38 = false ∨ valuation q 45 = false := by
  rw [value23, value38, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (149 : Vertex) (209 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 23 = false ∨ valuation q 45 = false ∨ valuation q 117 = false := by
  rw [value23, value41, value45, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (149 : Vertex) (221 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 38 = false ∨ valuation q 45 = false ∨ valuation q 117 = false := by
  rw [value38, value41, value45, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (209 : Vertex) (221 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 43 = false := by
  rw [value35, value38, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (209 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 45 = false := by
  rw [value35, value38, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (209 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value35, value42, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (201 : Vertex) (219 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value38, value42, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (217 : Vertex) (209 : Vertex) (219 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 167 = true ∨ valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 122 = true := by
  rw [value40, value42, value43, value122, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(211 : Vertex), (217 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (155 : Vertex) [(211 : Vertex), (217 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 167 = true ∨ valuation q 28 = true ∨ valuation q 42 = true ∨ valuation q 122 = true := by
  rw [value28, value42, value43, value122, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(155 : Vertex), (217 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (211 : Vertex) [(155 : Vertex), (217 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 123 = false := by
  rw [value44, value45, value46, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (221 : Vertex) (222 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 46 = true ∨ valuation q 123 = true := by
  rw [value44, value46, value123, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(222 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(222 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 42 = true ∨ valuation q 44 = true := by
  rw [value42, value44, value45, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(217 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (213 : Vertex) [(217 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 41 = true ∨ valuation q 42 = true := by
  rw [value41, value42, value45, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(213 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (220 : Vertex) [(213 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 36 = false ∨ valuation q 44 = false ∨ valuation q 124 = false := by
  rw [value36, value44, value46, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (206 : Vertex) (220 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 44 = true ∨ valuation q 124 = true := by
  rw [value44, value46, value124, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(220 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (206 : Vertex) [(220 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E153.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112153
