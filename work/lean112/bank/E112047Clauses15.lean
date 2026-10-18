import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 105 = false := by
  rw [value80, value85, value87, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 80 = false ∨ valuation q 89 = false ∨ valuation q 97 = false := by
  rw [value80, value87, value89, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 80 = false ∨ valuation q 89 = false ∨ valuation q 105 = false := by
  rw [value80, value87, value89, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 80 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value80, value87, value97, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 97 = false := by
  rw [value85, value87, value89, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 105 = false := by
  rw [value85, value87, value89, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (398 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value85, value87, value97, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value87, value89, value97, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (398 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 205 = true ∨ valuation q 21 = true ∨ valuation q 52 = true ∨ valuation q 80 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 105 = true := by
  rw [value21, value52, value80, value85, value87, value89, value105, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(138 : Vertex), (266 : Vertex), (386 : Vertex), (392 : Vertex), (398 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (410 : Vertex) [(138 : Vertex), (266 : Vertex), (386 : Vertex), (392 : Vertex), (398 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 205 = true ∨ valuation q 21 = true ∨ valuation q 52 = true ∨ valuation q 80 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 97 = true := by
  rw [value21, value52, value80, value85, value87, value89, value97, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(138 : Vertex), (266 : Vertex), (386 : Vertex), (392 : Vertex), (398 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (458 : Vertex) [(138 : Vertex), (266 : Vertex), (386 : Vertex), (392 : Vertex), (398 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value82, value85, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 85 = true ∨ valuation q 89 = true := by
  rw [value85, value88, value89, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(392 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (388 : Vertex) [(392 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 82 = true ∨ valuation q 89 = true := by
  rw [value82, value88, value89, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(388 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (392 : Vertex) [(388 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 82 = true ∨ valuation q 85 = true := by
  rw [value82, value85, value88, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(388 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (398 : Vertex) [(388 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 89 = true := by
  rw [value89, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (398 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 88 = true := by
  rw [value83, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ∈ [(390 : Vertex), (394 : Vertex), (396 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (398 : Vertex) [(390 : Vertex), (394 : Vertex), (396 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 87 = true ∨ valuation q 88 = true := by
  rw [value87, value88, value89, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(394 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (390 : Vertex) [(394 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 83 = true ∨ valuation q 88 = true := by
  rw [value83, value88, value89, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(390 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (394 : Vertex) [(390 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 83 = true ∨ valuation q 87 = true := by
  rw [value83, value87, value89, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (396 : Vertex) [(390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 91 = false := by
  rw [value25, value54, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (273 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 92 = false := by
  rw [value25, value54, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (273 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 96 = false := by
  rw [value25, value54, value90, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (273 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 110 = false := by
  rw [value25, value54, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (273 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value25, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value25, value90, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 91 = false ∨ valuation q 110 = false := by
  rw [value25, value90, value91, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (403 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value25, value90, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 92 = false ∨ valuation q 110 = false := by
  rw [value25, value90, value92, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (405 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 25 = false ∨ valuation q 96 = false ∨ valuation q 110 = false := by
  rw [value25, value90, value96, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (409 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 54 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value54, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 54 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value54, value90, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 54 = false ∨ valuation q 91 = false ∨ valuation q 110 = false := by
  rw [value54, value90, value91, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (273 : Vertex) (403 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E047.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112047
