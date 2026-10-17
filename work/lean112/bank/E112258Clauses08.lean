import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 43 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value43, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (321 : Vertex) (352 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 25 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value25, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (290 : Vertex) (352 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 25 = false ∨ valuation q 52 = false ∨ valuation q 58 = false := by
  rw [value25, value52, value54, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (290 : Vertex) (352 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 25 = false ∨ valuation q 55 = false ∨ valuation q 58 = false := by
  rw [value25, value54, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (290 : Vertex) (355 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 58 = false := by
  rw [value52, value54, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (354 : Vertex) (352 : Vertex) (355 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 176 = true ∨ valuation q 25 = true ∨ valuation q 52 = true ∨ valuation q 58 = true ∨ valuation q 111 = true := by
  rw [value25, value52, value54, value58, value111, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (354 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(290 : Vertex), (352 : Vertex), (362 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (354 : Vertex) (355 : Vertex) [(290 : Vertex), (352 : Vertex), (362 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 177 = true ∨ valuation q 54 = true := by
  rw [value54, value55, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(354 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (353 : Vertex) [(354 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 177 = true ∨ valuation q 53 = true := by
  rw [value53, value55, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(353 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (354 : Vertex) [(353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 178 = true ∨ valuation q 52 = true := by
  rw [value52, value56, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (484 : Vertex) → w ∈ [(352 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (484 : Vertex) [(352 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 29 = false ∨ valuation q 52 = false ∨ valuation q 58 = false := by
  rw [value29, value52, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (352 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 29 = false ∨ valuation q 52 = false ∨ valuation q 113 = false := by
  rw [value29, value52, value57, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (352 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 58 = false := by
  rw [value44, value52, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (328 : Vertex) (352 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 113 = false := by
  rw [value44, value52, value57, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (328 : Vertex) (352 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 180 = true ∨ valuation q 54 = true ∨ valuation q 57 = true ∨ valuation q 114 = true := by
  rw [value54, value57, value58, value114, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(354 : Vertex), (360 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (330 : Vertex) [(354 : Vertex), (360 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 180 = true ∨ valuation q 45 = true ∨ valuation q 54 = true ∨ valuation q 57 = true := by
  rw [value45, value54, value57, value58, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(330 : Vertex), (354 : Vertex), (360 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (490 : Vertex) [(330 : Vertex), (354 : Vertex), (360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 181 = true ∨ valuation q 52 = true := by
  rw [value52, value59, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(352 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (496 : Vertex) [(352 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 61 = false ∨ valuation q 119 = false := by
  rw [value61, value119, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (377 : Vertex) (379 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 182 = true ∨ valuation q 119 = true := by
  rw [value60, value119, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(505 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (379 : Vertex) [(505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 182 = true ∨ valuation q 61 = true := by
  rw [value60, value61, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(379 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (505 : Vertex) [(379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 183 = true ∨ valuation q 60 = true := by
  rw [value60, value61, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(377 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (347 : Vertex) [(377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 183 = true ∨ valuation q 49 = true := by
  rw [value49, value61, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(347 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (377 : Vertex) [(347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 50 = false ∨ valuation q 63 = false := by
  rw [value50, value63, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (380 : Vertex) (348 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 184 = true ∨ valuation q 63 = true := by
  rw [value62, value63, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(382 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (348 : Vertex) [(382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 184 = true ∨ valuation q 50 = true := by
  rw [value50, value62, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (380 : Vertex) w → w ∈ region → w ≠ (382 : Vertex) → w ∈ [(348 : Vertex)] := by decide
  have hg := other_cover q (380 : Vertex) (382 : Vertex) [(348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 185 = true ∨ valuation q 122 = true := by
  rw [value63, value122, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (380 : Vertex) → w ∈ [(510 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (380 : Vertex) [(510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 185 = true ∨ valuation q 62 = true := by
  rw [value62, value63, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(380 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (510 : Vertex) [(380 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value64, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 73 = false := by
  rw [value64, value65, value66, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 82 = false := by
  rw [value64, value65, value66, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 102 = false := by
  rw [value64, value65, value66, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (386 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value64, value65, value67, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (388 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 82 = false := by
  rw [value64, value65, value67, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (385 : Vertex) (388 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E258.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112258
