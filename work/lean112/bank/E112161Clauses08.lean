import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 73 = false := by
  rw [value48, value56, value57, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (278 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 168 = true ∨ valuation q 48 = true ∨ valuation q 73 = true ∨ valuation q 91 = true := by
  rw [value48, value57, value73, value91, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(263 : Vertex), (343 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (278 : Vertex) [(263 : Vertex), (343 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 168 = true ∨ valuation q 48 = true ∨ valuation q 56 = true ∨ valuation q 91 = true := by
  rw [value48, value56, value57, value91, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(263 : Vertex), (278 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (343 : Vertex) [(263 : Vertex), (278 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 168 = true ∨ valuation q 48 = true ∨ valuation q 56 = true ∨ valuation q 73 = true := by
  rw [value48, value56, value57, value73, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(263 : Vertex), (278 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (407 : Vertex) [(263 : Vertex), (278 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 49 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value49, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ∈ [(264 : Vertex), (281 : Vertex), (282 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (280 : Vertex) [(264 : Vertex), (281 : Vertex), (282 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 169 = true ∨ valuation q 59 = true ∨ valuation q 60 = true := by
  rw [value58, value59, value60, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(281 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (264 : Vertex) [(281 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 169 = true ∨ valuation q 49 = true ∨ valuation q 60 = true := by
  rw [value49, value58, value60, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(264 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (281 : Vertex) [(264 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 169 = true ∨ valuation q 49 = true ∨ valuation q 59 = true := by
  rw [value49, value58, value59, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(264 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (282 : Vertex) [(264 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 50 = false ∨ valuation q 58 = false ∨ valuation q 74 = false := by
  rw [value50, value58, value59, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 170 = true ∨ valuation q 58 = true ∨ valuation q 74 = true := by
  rw [value58, value59, value74, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(280 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (265 : Vertex) [(280 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 74 = true := by
  rw [value50, value59, value74, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(265 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (280 : Vertex) [(265 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 58 = true := by
  rw [value50, value58, value59, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(265 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (345 : Vertex) [(265 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 58 = false := by
  rw [value51, value54, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (266 : Vertex) (274 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 171 = true ∨ valuation q 51 = true ∨ valuation q 54 = true := by
  rw [value51, value54, value60, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(266 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (280 : Vertex) [(266 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 70 = false := by
  rw [value61, value62, value63, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (322 : Vertex) (324 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 172 = true ∨ valuation q 63 = true ∨ valuation q 70 = true := by
  rw [value61, value63, value70, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(324 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (322 : Vertex) [(324 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 172 = true ∨ valuation q 62 = true ∨ valuation q 70 = true := by
  rw [value61, value62, value70, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(322 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (324 : Vertex) [(322 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 44 = false ∨ valuation q 61 = false ∨ valuation q 66 = false := by
  rw [value44, value61, value62, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (320 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value61, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 173 = true ∨ valuation q 44 = true ∨ valuation q 65 = true ∨ valuation q 66 = true := by
  rw [value44, value62, value65, value66, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(258 : Vertex), (326 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (320 : Vertex) [(258 : Vertex), (326 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 173 = true ∨ valuation q 44 = true ∨ valuation q 61 = true ∨ valuation q 66 = true := by
  rw [value44, value61, value62, value66, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(258 : Vertex), (320 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (326 : Vertex) [(258 : Vertex), (320 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 173 = true ∨ valuation q 44 = true ∨ valuation q 61 = true ∨ valuation q 65 = true := by
  rw [value44, value61, value62, value65, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(258 : Vertex), (320 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (330 : Vertex) [(258 : Vertex), (320 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 68 = false := by
  rw [value61, value63, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (320 : Vertex) (325 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value61, value63, value65, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (320 : Vertex) (326 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 174 = true ∨ valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 65 = true := by
  rw [value61, value63, value64, value65, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(320 : Vertex), (325 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (332 : Vertex) [(320 : Vertex), (325 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 175 = true ∨ valuation q 46 = true ∨ valuation q 69 = true := by
  rw [value46, value64, value69, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(261 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (324 : Vertex) [(261 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 175 = true ∨ valuation q 46 = true ∨ valuation q 63 = true := by
  rw [value46, value63, value64, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(261 : Vertex), (324 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (333 : Vertex) [(261 : Vertex), (324 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 47 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value47, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (322 : Vertex) (324 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 63 = true := by
  rw [value47, value63, value65, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(262 : Vertex), (324 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (322 : Vertex) [(262 : Vertex), (324 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 67 = false := by
  rw [value51, value62, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (266 : Vertex) (322 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 177 = true ∨ valuation q 51 = true ∨ valuation q 67 = true := by
  rw [value51, value66, value67, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(266 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (322 : Vertex) [(266 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 177 = true ∨ valuation q 51 = true ∨ valuation q 62 = true := by
  rw [value51, value62, value66, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(266 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (331 : Vertex) [(266 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E161.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112161
