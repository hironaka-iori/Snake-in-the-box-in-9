import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 82 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value82, value94, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (403 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 82 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value82, value94, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value92, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value92, value94, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value92, value94, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value94, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (403 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 212 = true ∨ valuation q 82 = true ∨ valuation q 92 = true ∨ valuation q 96 = true ∨ valuation q 97 = true := by
  rw [value82, value92, value94, value96, value97, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (402 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(386 : Vertex), (400 : Vertex), (406 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (402 : Vertex) (403 : Vertex) [(386 : Vertex), (400 : Vertex), (406 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 83 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value83, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ∈ [(387 : Vertex), (401 : Vertex), (402 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (403 : Vertex) [(387 : Vertex), (401 : Vertex), (402 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value93, value94, value95, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(401 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (387 : Vertex) [(401 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 83 = true ∨ valuation q 94 = true := by
  rw [value83, value94, value95, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(387 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(387 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 213 = true ∨ valuation q 83 = true ∨ valuation q 93 = true := by
  rw [value83, value93, value95, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(387 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (402 : Vertex) [(387 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 96 = true := by
  rw [value96, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (406 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = true ∨ valuation q 100 = true ∨ valuation q 113 = true := by
  rw [value94, value96, value100, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ∈ [(402 : Vertex), (414 : Vertex), (470 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (406 : Vertex) [(402 : Vertex), (414 : Vertex), (470 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 100 = true ∨ valuation q 113 = true := by
  rw [value96, value100, value113, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(414 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (402 : Vertex) [(414 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 94 = true ∨ valuation q 113 = true := by
  rw [value94, value96, value113, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(402 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (414 : Vertex) [(402 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 214 = true ∨ valuation q 94 = true ∨ valuation q 100 = true := by
  rw [value94, value96, value100, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(402 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (470 : Vertex) [(402 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 31 = true ∨ valuation q 87 = true ∨ valuation q 94 = true ∨ valuation q 100 = true := by
  rw [value31, value87, value94, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ∈ [(154 : Vertex), (394 : Vertex), (402 : Vertex), (414 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (410 : Vertex) [(154 : Vertex), (394 : Vertex), (402 : Vertex), (414 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 31 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value31, value87, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (394 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 87 = false ∨ valuation q 94 = false ∨ valuation q 100 = false := by
  rw [value87, value94, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (394 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 94 = true ∨ valuation q 100 = true := by
  rw [value87, value94, value97, value100, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(394 : Vertex), (402 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (154 : Vertex) [(394 : Vertex), (402 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 31 = true ∨ valuation q 87 = true ∨ valuation q 100 = true := by
  rw [value31, value87, value97, value100, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(154 : Vertex), (394 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (402 : Vertex) [(154 : Vertex), (394 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 215 = true ∨ valuation q 31 = true ∨ valuation q 87 = true ∨ valuation q 94 = true := by
  rw [value31, value87, value94, value97, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(154 : Vertex), (394 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (414 : Vertex) [(154 : Vertex), (394 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 98 = true := by
  rw [value98, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (412 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 88 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value88, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ∈ [(396 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (412 : Vertex) [(396 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value88, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (396 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value88, value100, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (412 : Vertex) (396 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value98, value99, value100, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (396 : Vertex) [(413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 88 = true ∨ valuation q 100 = true := by
  rw [value88, value98, value100, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(396 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (413 : Vertex) [(396 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 216 = true ∨ valuation q 88 = true ∨ valuation q 99 = true := by
  rw [value88, value98, value99, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(396 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(396 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 98 = true := by
  rw [value98, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(412 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (397 : Vertex) [(412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 89 = true := by
  rw [value89, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(397 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (412 : Vertex) [(397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 90 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value90, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E027.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112027
