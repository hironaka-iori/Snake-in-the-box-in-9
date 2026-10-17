import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 40 = true ∨ valuation q 105 = true := by
  rw [value40, value41, value105, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(204 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (197 : Vertex) [(204 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 36 = true ∨ valuation q 105 = true := by
  rw [value36, value41, value105, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(197 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (204 : Vertex) [(197 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 36 = true ∨ valuation q 40 = true := by
  rw [value36, value40, value41, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(197 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (461 : Vertex) [(197 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 47 = true := by
  rw [value42, value47, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (213 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 43 = true := by
  rw [value42, value43, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(213 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (217 : Vertex) [(213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value36, value42, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (213 : Vertex) (197 : Vertex) (209 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 45 = true := by
  rw [value36, value43, value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(197 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (209 : Vertex) [(197 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 42 = true := by
  rw [value36, value42, value43, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(197 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (215 : Vertex) [(197 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 50 = true ∨ valuation q 112 = true := by
  rw [value44, value50, value112, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(222 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (215 : Vertex) [(222 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 45 = true ∨ valuation q 112 = true := by
  rw [value44, value45, value112, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(215 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(215 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 45 = true ∨ valuation q 50 = true := by
  rw [value44, value45, value50, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(215 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (470 : Vertex) [(215 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value37, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 113 = false := by
  rw [value37, value43, value45, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 44 = false ∨ valuation q 113 = false := by
  rw [value37, value44, value45, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (214 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 113 = false := by
  rw [value43, value44, value45, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (213 : Vertex) (214 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 13 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value13, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 29 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value29, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (152 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 114 = false := by
  rw [value46, value47, value48, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (217 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 165 = true ∨ valuation q 46 = true ∨ valuation q 49 = true := by
  rw [value46, value47, value49, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(216 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (209 : Vertex) [(216 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 165 = true ∨ valuation q 42 = true ∨ valuation q 49 = true := by
  rw [value42, value47, value49, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(209 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (216 : Vertex) [(209 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 165 = true ∨ valuation q 42 = true ∨ valuation q 46 = true := by
  rw [value42, value46, value47, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(209 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (219 : Vertex) [(209 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 50 = false := by
  rw [value38, value46, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (202 : Vertex) (216 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 38 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value38, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (202 : Vertex) (219 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value46, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (216 : Vertex) (219 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 166 = true ∨ valuation q 38 = true ∨ valuation q 49 = true ∨ valuation q 50 = true := by
  rw [value38, value48, value49, value50, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(202 : Vertex), (219 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (216 : Vertex) [(202 : Vertex), (219 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value39, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 117 = false := by
  rw [value44, value48, value50, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 1 = false ∨ valuation q 55 = false ∨ valuation q 79 = false := by
  rw [value1, value51, value55, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (278 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 1 = true ∨ valuation q 79 = true := by
  rw [value1, value51, value79, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(6 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (278 : Vertex) [(6 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true ∨ valuation q 55 = true := by
  rw [value54, value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(278 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (272 : Vertex) [(278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 70 = false := by
  rw [value51, value54, value55, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 51 = true ∨ valuation q 70 = true := by
  rw [value51, value55, value70, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(262 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (274 : Vertex) [(262 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E096.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112096
