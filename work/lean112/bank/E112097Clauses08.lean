import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 183 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value59, value60, value61, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (309 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(308 : Vertex), (311 : Vertex)] := by decide
  have hg := other_cover q (309 : Vertex) (305 : Vertex) [(308 : Vertex), (311 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 183 = true ∨ valuation q 57 = true ∨ valuation q 59 = true := by
  rw [value57, value59, value60, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (309 : Vertex) w → w ∈ region → w ≠ (311 : Vertex) → w ∈ [(305 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (309 : Vertex) (311 : Vertex) [(305 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 184 = true ∨ valuation q 58 = true ∨ valuation q 60 = true := by
  rw [value58, value60, value61, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (311 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(307 : Vertex), (309 : Vertex)] := by decide
  have hg := other_cover q (311 : Vertex) (295 : Vertex) [(307 : Vertex), (309 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 184 = true ∨ valuation q 51 = true ∨ valuation q 60 = true := by
  rw [value51, value60, value61, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (311 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(295 : Vertex), (309 : Vertex)] := by decide
  have hg := other_cover q (311 : Vertex) (307 : Vertex) [(295 : Vertex), (309 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 184 = true ∨ valuation q 51 = true ∨ valuation q 58 = true := by
  rw [value51, value58, value61, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (311 : Vertex) w → w ∈ region → w ≠ (309 : Vertex) → w ∈ [(295 : Vertex), (307 : Vertex)] := by decide
  have hg := other_cover q (311 : Vertex) (309 : Vertex) [(295 : Vertex), (307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 53 = false ∨ valuation q 57 = false ∨ valuation q 64 = false := by
  rw [value53, value57, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (313 : Vertex) (297 : Vertex) (305 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 185 = true ∨ valuation q 57 = true ∨ valuation q 64 = true := by
  rw [value57, value62, value64, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(305 : Vertex), (315 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (297 : Vertex) [(305 : Vertex), (315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 185 = true ∨ valuation q 53 = true ∨ valuation q 64 = true := by
  rw [value53, value62, value64, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(297 : Vertex), (315 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (305 : Vertex) [(297 : Vertex), (315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 185 = true ∨ valuation q 53 = true ∨ valuation q 57 = true := by
  rw [value53, value57, value62, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (313 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(297 : Vertex), (305 : Vertex)] := by decide
  have hg := other_cover q (313 : Vertex) (315 : Vertex) [(297 : Vertex), (305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 186 = true ∨ valuation q 64 = true := by
  rw [value63, value64, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (298 : Vertex) → w ∈ [(315 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (298 : Vertex) [(315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 186 = true ∨ valuation q 54 = true := by
  rw [value54, value63, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(298 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (315 : Vertex) [(298 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value58, value62, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (315 : Vertex) (307 : Vertex) (313 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 187 = true ∨ valuation q 62 = true ∨ valuation q 63 = true := by
  rw [value62, value63, value64, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(313 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (307 : Vertex) [(313 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 187 = true ∨ valuation q 58 = true ∨ valuation q 63 = true := by
  rw [value58, value63, value64, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (313 : Vertex) → w ∈ [(307 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (313 : Vertex) [(307 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 187 = true ∨ valuation q 58 = true ∨ valuation q 62 = true := by
  rw [value58, value62, value64, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(307 : Vertex), (313 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (314 : Vertex) [(307 : Vertex), (313 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value65, value66, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (355 : Vertex) (357 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 71 = false ∨ valuation q 102 = false := by
  rw [value65, value66, value71, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (355 : Vertex) (361 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 188 = true ∨ valuation q 67 = true ∨ valuation q 71 = true ∨ valuation q 102 = true := by
  rw [value65, value67, value71, value102, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(357 : Vertex), (361 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (355 : Vertex) [(357 : Vertex), (361 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 188 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 102 = true := by
  rw [value65, value66, value67, value102, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(355 : Vertex), (357 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (361 : Vertex) [(355 : Vertex), (357 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value65, value66, value69, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (353 : Vertex) (359 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 189 = true ∨ valuation q 65 = true ∨ valuation q 69 = true := by
  rw [value65, value66, value69, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(353 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (371 : Vertex) [(353 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 105 = false := by
  rw [value65, value67, value69, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (353 : Vertex) (359 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 190 = true ∨ valuation q 65 = true ∨ valuation q 69 = true := by
  rw [value65, value67, value69, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(353 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (485 : Vertex) [(353 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 50 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value50, value68, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (358 : Vertex) (294 : Vertex) (359 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 50 = false ∨ valuation q 72 = false ∨ valuation q 106 = false := by
  rw [value50, value68, value72, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (358 : Vertex) (294 : Vertex) (366 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 106 = false := by
  rw [value68, value69, value72, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (358 : Vertex) (359 : Vertex) (366 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 51 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value51, value66, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (355 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 51 = false ∨ valuation q 66 = false ∨ valuation q 73 = false := by
  rw [value51, value66, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (355 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 73 = false := by
  rw [value67, value68, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (357 : Vertex) (358 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 192 = true ∨ valuation q 51 = true ∨ valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 73 = true := by
  rw [value51, value67, value68, value69, value73, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(295 : Vertex), (357 : Vertex), (358 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (355 : Vertex) [(295 : Vertex), (357 : Vertex), (358 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 192 = true ∨ valuation q 51 = true ∨ valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 73 = true := by
  rw [value51, value66, value68, value69, value73, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(295 : Vertex), (355 : Vertex), (358 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (357 : Vertex) [(295 : Vertex), (355 : Vertex), (358 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 78 = false ∨ valuation q 107 = false := by
  rw [value52, value70, value78, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (376 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E097.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112097
