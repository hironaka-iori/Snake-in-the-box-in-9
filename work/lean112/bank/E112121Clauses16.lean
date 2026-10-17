import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 194 = true ∨ valuation q 61 = true ∨ valuation q 67 = true := by
  rw [value61, value67, value68, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(191 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (247 : Vertex) [(191 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 8 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value8, value69, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (32 : Vertex) (289 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 8 = false ∨ valuation q 70 = false ∨ valuation q 87 = false := by
  rw [value8, value69, value70, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (32 : Vertex) (289 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 8 = false ∨ valuation q 73 = false ∨ valuation q 87 = false := by
  rw [value8, value69, value73, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (32 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 195 = true ∨ valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 87 = true := by
  rw [value69, value70, value73, value87, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (32 : Vertex) → w ∈ [(289 : Vertex), (296 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (32 : Vertex) [(289 : Vertex), (296 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 195 = true ∨ valuation q 8 = true ∨ valuation q 73 = true ∨ valuation q 87 = true := by
  rw [value8, value69, value73, value87, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(32 : Vertex), (296 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (289 : Vertex) [(32 : Vertex), (296 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 195 = true ∨ valuation q 8 = true ∨ valuation q 70 = true ∨ valuation q 87 = true := by
  rw [value8, value69, value70, value87, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(32 : Vertex), (289 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (296 : Vertex) [(32 : Vertex), (289 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 195 = true ∨ valuation q 8 = true ∨ valuation q 70 = true ∨ valuation q 73 = true := by
  rw [value8, value69, value70, value73, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(32 : Vertex), (289 : Vertex), (296 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (416 : Vertex) [(32 : Vertex), (289 : Vertex), (296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 9 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value9, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (288 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 9 = false ∨ valuation q 69 = false ∨ valuation q 78 = false := by
  rw [value9, value69, value70, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (288 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 9 = false ∨ valuation q 69 = false ∨ valuation q 88 = false := by
  rw [value9, value69, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (288 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 9 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value9, value70, value74, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (297 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 9 = false ∨ valuation q 74 = false ∨ valuation q 88 = false := by
  rw [value9, value70, value74, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (297 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 9 = false ∨ valuation q 78 = false ∨ valuation q 88 = false := by
  rw [value9, value70, value78, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 78 = false := by
  rw [value69, value70, value74, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (288 : Vertex) (297 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 88 = false := by
  rw [value69, value70, value74, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (288 : Vertex) (297 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 78 = false ∨ valuation q 88 = false := by
  rw [value69, value70, value78, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (288 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 78 = false ∨ valuation q 88 = false := by
  rw [value70, value74, value78, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (297 : Vertex) (305 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 196 = true ∨ valuation q 9 = true ∨ valuation q 69 = true ∨ valuation q 78 = true ∨ valuation q 88 = true := by
  rw [value9, value69, value70, value78, value88, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(33 : Vertex), (288 : Vertex), (305 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (297 : Vertex) [(33 : Vertex), (288 : Vertex), (305 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 13 = false ∨ valuation q 72 = false ∨ valuation q 92 = false := by
  rw [value13, value71, value72, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (38 : Vertex) (295 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 13 = false ∨ valuation q 82 = false ∨ valuation q 92 = false := by
  rw [value13, value71, value82, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (38 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 92 = false := by
  rw [value71, value72, value82, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (295 : Vertex) (310 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 197 = true ∨ valuation q 72 = true ∨ valuation q 82 = true ∨ valuation q 92 = true := by
  rw [value71, value72, value82, value92, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(295 : Vertex), (310 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (38 : Vertex) [(295 : Vertex), (310 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 197 = true ∨ valuation q 13 = true ∨ valuation q 82 = true ∨ valuation q 92 = true := by
  rw [value13, value71, value82, value92, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(38 : Vertex), (310 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (295 : Vertex) [(38 : Vertex), (310 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 197 = true ∨ valuation q 13 = true ∨ valuation q 72 = true ∨ valuation q 92 = true := by
  rw [value13, value71, value72, value92, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(38 : Vertex), (295 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (310 : Vertex) [(38 : Vertex), (295 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 197 = true ∨ valuation q 13 = true ∨ valuation q 72 = true ∨ valuation q 82 = true := by
  rw [value13, value71, value72, value82, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (294 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(38 : Vertex), (295 : Vertex), (310 : Vertex)] := by decide
  have hg := other_cover q (294 : Vertex) (422 : Vertex) [(38 : Vertex), (295 : Vertex), (310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 71 = false ∨ valuation q 77 = false := by
  rw [value14, value71, value72, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (294 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 71 = false ∨ valuation q 93 = false := by
  rw [value14, value71, value72, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (294 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 14 = false ∨ valuation q 77 = false ∨ valuation q 93 = false := by
  rw [value14, value72, value77, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (39 : Vertex) (303 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 93 = false := by
  rw [value71, value72, value77, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (294 : Vertex) (303 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 14 = false ∨ valuation q 71 = false := by
  rw [value14, value71, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (295 : Vertex) (39 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 198 = true ∨ valuation q 14 = true ∨ valuation q 77 = true ∨ valuation q 93 = true := by
  rw [value14, value72, value77, value93, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(39 : Vertex), (303 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (294 : Vertex) [(39 : Vertex), (303 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block16 (q : Snake 81) (h : Conditions q) : B112E121.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112121
