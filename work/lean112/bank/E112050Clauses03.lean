import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 15 = false ∨ valuation q 32 = false ∨ valuation q 37 = false := by
  rw [value15, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (192 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 15 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value15, value33, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (198 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value33, value34, value35, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (199 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 43 = false := by
  rw [value33, value34, value35, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 33 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value33, value34, value39, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value34, value35, value39, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (199 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 33 = false ∨ valuation q 43 = false := by
  rw [value33, value43, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (198 : Vertex) (194 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 162 = true ∨ valuation q 33 = true ∨ valuation q 39 = true ∨ valuation q 43 = true := by
  rw [value33, value34, value39, value43, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(194 : Vertex), (206 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (199 : Vertex) [(194 : Vertex), (206 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 162 = true ∨ valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 39 = true := by
  rw [value33, value34, value35, value39, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(194 : Vertex), (199 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (214 : Vertex) [(194 : Vertex), (199 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 44 = true ∨ valuation q 114 = true := by
  rw [value35, value44, value114, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(215 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (198 : Vertex) [(215 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 34 = true ∨ valuation q 114 = true := by
  rw [value34, value35, value114, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(198 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (215 : Vertex) [(198 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 34 = true ∨ valuation q 44 = true := by
  rw [value34, value35, value44, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(198 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (455 : Vertex) [(198 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 37 = true ∨ valuation q 38 = true := by
  rw [value36, value37, value38, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(202 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(202 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value32, value36, value38, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(192 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (202 : Vertex) [(192 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 164 = true ∨ valuation q 32 = true ∨ valuation q 37 = true := by
  rw [value32, value36, value37, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(192 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (204 : Vertex) [(192 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 39 = false := by
  rw [value33, value36, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 46 = false := by
  rw [value33, value36, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (200 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 39 = false ∨ valuation q 46 = false := by
  rw [value33, value37, value39, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (206 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 46 = false := by
  rw [value36, value37, value39, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (200 : Vertex) (206 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 3 = false ∨ valuation q 21 = false ∨ valuation q 36 = false := by
  rw [value3, value21, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 3 = false ∨ valuation q 36 = false ∨ valuation q 39 = false := by
  rw [value3, value36, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 21 = false ∨ valuation q 36 = false ∨ valuation q 39 = false := by
  rw [value21, value36, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 3 = false ∨ valuation q 36 = false := by
  rw [value3, value36, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (204 : Vertex) (76 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 166 = true ∨ valuation q 21 = true ∨ valuation q 36 = true ∨ valuation q 39 = true := by
  rw [value21, value36, value38, value39, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(140 : Vertex), (200 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (76 : Vertex) [(140 : Vertex), (200 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 23 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value23, value34, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (142 : Vertex) (198 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value34, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (202 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 118 = false := by
  rw [value34, value37, value39, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (202 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 118 = false := by
  rw [value34, value38, value39, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 167 = true ∨ valuation q 23 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 118 = true := by
  rw [value23, value34, value37, value39, value118, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(142 : Vertex), (198 : Vertex), (202 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (204 : Vertex) [(142 : Vertex), (198 : Vertex), (202 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 168 = true ∨ valuation q 42 = true := by
  rw [value40, value42, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(213 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (217 : Vertex) [(213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value42, value43, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (212 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 169 = true ∨ valuation q 43 = true := by
  rw [value41, value43, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(214 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (213 : Vertex) [(214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E050.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112050
