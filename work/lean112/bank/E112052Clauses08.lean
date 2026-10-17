import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 183 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 58 = true ∨ valuation q 74 = true := by
  rw [value52, value56, value57, value58, value74, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(260 : Vertex), (269 : Vertex), (270 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (284 : Vertex) [(260 : Vertex), (269 : Vertex), (270 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 183 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 58 = true ∨ valuation q 64 = true := by
  rw [value52, value56, value57, value58, value64, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(260 : Vertex), (269 : Vertex), (270 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (332 : Vertex) [(260 : Vertex), (269 : Vertex), (270 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value53, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 95 = false := by
  rw [value53, value54, value57, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 95 = false := by
  rw [value53, value56, value57, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 95 = false := by
  rw [value54, value56, value57, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 184 = true ∨ valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 95 = true := by
  rw [value54, value56, value57, value95, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(265 : Vertex), (268 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (261 : Vertex) [(265 : Vertex), (268 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 184 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 95 = true := by
  rw [value53, value56, value57, value95, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(261 : Vertex), (268 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (265 : Vertex) [(261 : Vertex), (268 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 65 = false ∨ valuation q 96 = false := by
  rw [value56, value58, value65, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (268 : Vertex) (286 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 185 = true ∨ valuation q 56 = true ∨ valuation q 96 = true := by
  rw [value56, value58, value96, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(268 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (286 : Vertex) [(268 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 186 = true ∨ valuation q 63 = true := by
  rw [value59, value63, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(280 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (274 : Vertex) [(280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 186 = true ∨ valuation q 60 = true := by
  rw [value59, value60, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(274 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (280 : Vertex) [(274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 50 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value50, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (258 : Vertex) (272 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value59, value60, value61, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(272 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (258 : Vertex) [(272 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 50 = true ∨ valuation q 61 = true := by
  rw [value50, value60, value61, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(258 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (272 : Vertex) [(258 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 187 = true ∨ valuation q 50 = true ∨ valuation q 59 = true := by
  rw [value50, value59, value60, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(258 : Vertex), (272 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (275 : Vertex) [(258 : Vertex), (272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value51, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (259 : Vertex) (274 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 188 = true ∨ valuation q 60 = true ∨ valuation q 62 = true := by
  rw [value60, value61, value62, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(274 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (259 : Vertex) [(274 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 188 = true ∨ valuation q 51 = true ∨ valuation q 62 = true := by
  rw [value51, value61, value62, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(259 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (274 : Vertex) [(259 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 66 = false ∨ valuation q 101 = false := by
  rw [value61, value62, value66, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (275 : Vertex) (287 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 79 = false ∨ valuation q 101 = false := by
  rw [value61, value62, value79, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (275 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 66 = true ∨ valuation q 79 = true ∨ valuation q 101 = true := by
  rw [value62, value66, value79, value101, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(287 : Vertex), (343 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (275 : Vertex) [(287 : Vertex), (343 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 61 = true ∨ valuation q 79 = true ∨ valuation q 101 = true := by
  rw [value61, value62, value79, value101, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(275 : Vertex), (343 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(275 : Vertex), (343 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 61 = true ∨ valuation q 66 = true ∨ valuation q 101 = true := by
  rw [value61, value62, value66, value101, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(275 : Vertex), (287 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (343 : Vertex) [(275 : Vertex), (287 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 189 = true ∨ valuation q 61 = true ∨ valuation q 66 = true ∨ valuation q 79 = true := by
  rw [value61, value62, value66, value79, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(275 : Vertex), (287 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (407 : Vertex) [(275 : Vertex), (287 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 190 = true ∨ valuation q 64 = true ∨ valuation q 80 = true := by
  rw [value63, value64, value80, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(284 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (272 : Vertex) [(284 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 190 = true ∨ valuation q 59 = true ∨ valuation q 80 = true := by
  rw [value59, value63, value80, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(272 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (284 : Vertex) [(272 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 56 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value56, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (268 : Vertex) (280 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 63 = true ∨ valuation q 65 = true := by
  rw [value63, value64, value65, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(280 : Vertex), (286 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (268 : Vertex) [(280 : Vertex), (286 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 56 = true ∨ valuation q 65 = true := by
  rw [value56, value64, value65, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(268 : Vertex), (286 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (280 : Vertex) [(268 : Vertex), (286 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 191 = true ∨ valuation q 56 = true ∨ valuation q 63 = true := by
  rw [value56, value63, value64, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(268 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (286 : Vertex) [(268 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 106 = false := by
  rw [value64, value65, value66, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (286 : Vertex) (284 : Vertex) (287 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E052.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112052
