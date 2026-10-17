import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 214 = true ∨ valuation q 35 = true ∨ valuation q 98 = true ∨ valuation q 108 = true := by
  rw [value35, value90, value98, value108, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(137 : Vertex), (409 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (392 : Vertex) [(137 : Vertex), (409 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 91 = true := by
  rw [value91, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (398 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 87 = true ∨ valuation q 92 = true ∨ valuation q 112 = true := by
  rw [value87, value91, value92, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ∈ [(390 : Vertex), (399 : Vertex), (462 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (398 : Vertex) [(390 : Vertex), (399 : Vertex), (462 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 92 = true ∨ valuation q 112 = true := by
  rw [value91, value92, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(399 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (390 : Vertex) [(399 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 112 = true := by
  rw [value87, value91, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(390 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (399 : Vertex) [(390 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 87 = true ∨ valuation q 92 = true := by
  rw [value87, value91, value92, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (462 : Vertex) [(390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 113 = false := by
  rw [value88, value91, value92, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (391 : Vertex) (398 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 216 = true ∨ valuation q 91 = true ∨ valuation q 113 = true := by
  rw [value91, value92, value113, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(398 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (391 : Vertex) [(398 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 216 = true ∨ valuation q 88 = true ∨ valuation q 113 = true := by
  rw [value88, value92, value113, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(391 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (398 : Vertex) [(391 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 93 = true := by
  rw [value93, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (403 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 96 = true ∨ valuation q 100 = true := by
  rw [value93, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ∈ [(407 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (403 : Vertex) [(407 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 217 = true ∨ valuation q 100 = true := by
  rw [value93, value100, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(411 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (407 : Vertex) [(411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 217 = true ∨ valuation q 96 = true := by
  rw [value93, value96, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(407 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (411 : Vertex) [(407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 101 = false ∨ valuation q 117 = false := by
  rw [value94, value95, value101, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (405 : Vertex) (412 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 218 = true ∨ valuation q 101 = true ∨ valuation q 117 = true := by
  rw [value94, value101, value117, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(412 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (405 : Vertex) [(412 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 218 = true ∨ valuation q 95 = true ∨ valuation q 117 = true := by
  rw [value94, value95, value117, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(405 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (412 : Vertex) [(405 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 218 = true ∨ valuation q 95 = true ∨ valuation q 101 = true := by
  rw [value94, value95, value101, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(405 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (468 : Vertex) [(405 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 95 = true := by
  rw [value95, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (405 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 86 = true ∨ valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 118 = true := by
  rw [value86, value94, value95, value96, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ∈ [(389 : Vertex), (404 : Vertex), (407 : Vertex), (469 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (405 : Vertex) [(389 : Vertex), (404 : Vertex), (407 : Vertex), (469 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 86 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value86, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (404 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 86 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value86, value94, value95, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (404 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 118 = false := by
  rw [value94, value95, value96, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (404 : Vertex) (407 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 118 = true := by
  rw [value94, value95, value96, value118, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(404 : Vertex), (407 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (389 : Vertex) [(404 : Vertex), (407 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 86 = true ∨ valuation q 96 = true ∨ valuation q 118 = true := by
  rw [value86, value95, value96, value118, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(389 : Vertex), (407 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (404 : Vertex) [(389 : Vertex), (407 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 86 = true ∨ valuation q 94 = true ∨ valuation q 118 = true := by
  rw [value86, value94, value95, value118, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(389 : Vertex), (404 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (407 : Vertex) [(389 : Vertex), (404 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 86 = true ∨ valuation q 94 = true ∨ valuation q 96 = true := by
  rw [value86, value94, value95, value96, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(389 : Vertex), (404 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (469 : Vertex) [(389 : Vertex), (404 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value88, value93, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 220 = true ∨ valuation q 88 = true ∨ valuation q 95 = true := by
  rw [value88, value95, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(391 : Vertex), (405 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (403 : Vertex) [(391 : Vertex), (405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 220 = true ∨ valuation q 88 = true ∨ valuation q 93 = true := by
  rw [value88, value93, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(391 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (405 : Vertex) [(391 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value89, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value89, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (409 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value89, value97, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (392 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E105.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112105
