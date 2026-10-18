import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 52 = false ∨ valuation q 81 = false ∨ valuation q 98 = false := by
  rw [value52, value81, value88, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 52 = false ∨ valuation q 81 = false ∨ valuation q 106 = false := by
  rw [value52, value81, value88, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (386 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 52 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value52, value86, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 52 = false ∨ valuation q 86 = false ∨ valuation q 98 = false := by
  rw [value52, value86, value88, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (392 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 52 = false ∨ valuation q 86 = false ∨ valuation q 106 = false := by
  rw [value52, value86, value88, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (392 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 52 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value52, value88, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 52 = false ∨ valuation q 90 = false ∨ valuation q 106 = false := by
  rw [value52, value88, value90, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (398 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 52 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value52, value88, value98, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (266 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value81, value86, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 98 = false := by
  rw [value81, value86, value88, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 106 = false := by
  rw [value81, value86, value88, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (392 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value81, value88, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 90 = false ∨ valuation q 106 = false := by
  rw [value81, value88, value90, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (398 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value81, value88, value98, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (386 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value86, value88, value90, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (398 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 106 = false := by
  rw [value86, value88, value90, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (398 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value86, value88, value98, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (392 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value88, value90, value98, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (394 : Vertex) (398 : Vertex) (410 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 21 = true ∨ valuation q 81 = true ∨ valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value21, value81, value86, value88, value90, value98, value106, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(138 : Vertex), (386 : Vertex), (392 : Vertex), (398 : Vertex), (410 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (266 : Vertex) [(138 : Vertex), (386 : Vertex), (392 : Vertex), (398 : Vertex), (410 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 206 = true ∨ valuation q 21 = true ∨ valuation q 52 = true ∨ valuation q 81 = true ∨ valuation q 86 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value21, value52, value81, value86, value88, value98, value106, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (394 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(138 : Vertex), (266 : Vertex), (386 : Vertex), (392 : Vertex), (410 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (394 : Vertex) (398 : Vertex) [(138 : Vertex), (266 : Vertex), (386 : Vertex), (392 : Vertex), (410 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value83, value86, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (388 : Vertex) (392 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 86 = true ∨ valuation q 90 = true := by
  rw [value86, value89, value90, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(392 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (388 : Vertex) [(392 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 207 = true ∨ valuation q 83 = true ∨ valuation q 86 = true := by
  rw [value83, value86, value89, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(388 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (398 : Vertex) [(388 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 90 = true := by
  rw [value90, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (398 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 89 = true := by
  rw [value84, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ∈ [(390 : Vertex), (394 : Vertex), (396 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (398 : Vertex) [(390 : Vertex), (394 : Vertex), (396 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 84 = false ∨ valuation q 88 = false := by
  rw [value84, value88, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (398 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 88 = true ∨ valuation q 89 = true := by
  rw [value88, value89, value90, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(394 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (390 : Vertex) [(394 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 84 = true ∨ valuation q 89 = true := by
  rw [value84, value89, value90, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(390 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (394 : Vertex) [(390 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 208 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value84, value88, value90, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (396 : Vertex) [(390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 92 = false := by
  rw [value25, value54, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (273 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 93 = false := by
  rw [value25, value54, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (273 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 25 = false ∨ valuation q 54 = false ∨ valuation q 97 = false := by
  rw [value25, value54, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (273 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E007.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112007
