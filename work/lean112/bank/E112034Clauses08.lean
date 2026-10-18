import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 186 = true ∨ valuation q 4 = true ∨ valuation q 57 = true ∨ valuation q 75 = true := by
  rw [value4, value57, value58, value75, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(43 : Vertex), (298 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (315 : Vertex) [(43 : Vertex), (298 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 186 = true ∨ valuation q 4 = true ∨ valuation q 57 = true ∨ valuation q 66 = true := by
  rw [value4, value57, value58, value66, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(43 : Vertex), (298 : Vertex), (315 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (363 : Vertex) [(43 : Vertex), (298 : Vertex), (315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value53, value56, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (292 : Vertex) (296 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 187 = true ∨ valuation q 53 = true ∨ valuation q 56 = true := by
  rw [value53, value56, value59, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(292 : Vertex), (296 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (302 : Vertex) [(292 : Vertex), (296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 188 = true ∨ valuation q 57 = true ∨ valuation q 59 = true := by
  rw [value57, value59, value60, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(298 : Vertex), (300 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (294 : Vertex) [(298 : Vertex), (300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 188 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value55, value57, value60, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(294 : Vertex), (298 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (300 : Vertex) [(294 : Vertex), (298 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 54 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value54, value61, value63, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (309 : Vertex) (293 : Vertex) (311 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 189 = true ∨ valuation q 63 = true ∨ valuation q 67 = true := by
  rw [value61, value63, value67, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (309 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(311 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (309 : Vertex) (293 : Vertex) [(311 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 189 = true ∨ valuation q 54 = true ∨ valuation q 67 = true := by
  rw [value54, value61, value67, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (309 : Vertex) w → w ∈ region → w ≠ (311 : Vertex) → w ∈ [(293 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (309 : Vertex) (311 : Vertex) [(293 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 189 = true ∨ valuation q 54 = true ∨ valuation q 63 = true := by
  rw [value54, value61, value63, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (309 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(293 : Vertex), (311 : Vertex)] := by decide
  have hg := other_cover q (309 : Vertex) (317 : Vertex) [(293 : Vertex), (311 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 63 = true := by
  rw [value62, value63, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(311 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (294 : Vertex) [(311 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 55 = true := by
  rw [value55, value62, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (311 : Vertex) → w ∈ [(294 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (311 : Vertex) [(294 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 68 = false := by
  rw [value61, value62, value63, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (311 : Vertex) (309 : Vertex) (310 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 191 = true ∨ valuation q 62 = true ∨ valuation q 68 = true := by
  rw [value62, value63, value68, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (311 : Vertex) w → w ∈ region → w ≠ (309 : Vertex) → w ∈ [(310 : Vertex), (319 : Vertex)] := by decide
  have hg := other_cover q (311 : Vertex) (309 : Vertex) [(310 : Vertex), (319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 191 = true ∨ valuation q 61 = true ∨ valuation q 68 = true := by
  rw [value61, value63, value68, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (311 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(309 : Vertex), (319 : Vertex)] := by decide
  have hg := other_cover q (311 : Vertex) (310 : Vertex) [(309 : Vertex), (319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 9 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value9, value56, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (56 : Vertex) (296 : Vertex) (313 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 9 = false ∨ valuation q 56 = false ∨ valuation q 82 = false := by
  rw [value9, value56, value64, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (56 : Vertex) (296 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 9 = false ∨ valuation q 65 = false ∨ valuation q 82 = false := by
  rw [value9, value64, value65, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (56 : Vertex) (313 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 56 = false ∨ valuation q 65 = false ∨ valuation q 82 = false := by
  rw [value56, value64, value65, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (296 : Vertex) (313 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value64, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (313 : Vertex) (312 : Vertex) (315 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 66 = true ∨ valuation q 67 = true := by
  rw [value65, value66, value67, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (312 : Vertex) → w ∈ [(315 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (312 : Vertex) [(315 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value64, value65, value67, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(312 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (315 : Vertex) [(312 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 64 = true ∨ valuation q 66 = true := by
  rw [value64, value65, value66, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(312 : Vertex), (315 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (317 : Vertex) [(312 : Vertex), (315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 58 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value58, value65, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (315 : Vertex) (299 : Vertex) (313 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 194 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value65, value66, value68, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(313 : Vertex), (319 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (299 : Vertex) [(313 : Vertex), (319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 194 = true ∨ valuation q 58 = true ∨ valuation q 68 = true := by
  rw [value58, value66, value68, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (313 : Vertex) → w ∈ [(299 : Vertex), (319 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (313 : Vertex) [(299 : Vertex), (319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value61, value65, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (309 : Vertex) (313 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 103 = false := by
  rw [value61, value65, value67, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (309 : Vertex) (313 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 103 = false := by
  rw [value65, value67, value68, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (313 : Vertex) (319 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 12 = false ∨ valuation q 63 = false ∨ valuation q 66 = false := by
  rw [value12, value63, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (63 : Vertex) (311 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 12 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value12, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (63 : Vertex) (311 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 85 = false := by
  rw [value63, value66, value68, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (311 : Vertex) (315 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E034.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112034
