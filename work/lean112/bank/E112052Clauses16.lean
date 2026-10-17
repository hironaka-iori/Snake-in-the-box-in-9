import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 215 = true ∨ valuation q 53 = true ∨ valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 99 = true ∨ valuation q 112 = true := by
  rw [value53, value87, value88, value90, value95, value99, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (389 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(261 : Vertex), (388 : Vertex), (391 : Vertex), (397 : Vertex), (405 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (389 : Vertex) (133 : Vertex) [(261 : Vertex), (388 : Vertex), (391 : Vertex), (397 : Vertex), (405 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value86, value87, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 96 = false := by
  rw [value86, value87, value89, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value86, value87, value89, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 96 = false := by
  rw [value86, value89, value90, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 90 = false ∨ valuation q 100 = false := by
  rw [value86, value89, value90, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 86 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value86, value89, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 96 = false := by
  rw [value87, value89, value90, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (388 : Vertex) (391 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 100 = false := by
  rw [value87, value89, value90, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (388 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 87 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value87, value89, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (388 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value89, value90, value96, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (391 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 96 = true ∨ valuation q 100 = true := by
  rw [value86, value87, value89, value96, value100, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex), (398 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (391 : Vertex) [(386 : Vertex), (388 : Vertex), (398 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 96 = true := by
  rw [value86, value87, value89, value90, value96, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex), (391 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (406 : Vertex) [(386 : Vertex), (388 : Vertex), (391 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 101 = false := by
  rw [value88, value89, value90, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (389 : Vertex) (390 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 113 = false := by
  rw [value88, value89, value90, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (389 : Vertex) (390 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 113 = false := by
  rw [value88, value90, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (389 : Vertex) (407 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 89 = false ∨ valuation q 101 = false ∨ valuation q 113 = false := by
  rw [value89, value90, value101, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (390 : Vertex) (407 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 89 = true ∨ valuation q 101 = true ∨ valuation q 113 = true := by
  rw [value89, value90, value101, value113, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(390 : Vertex), (407 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (389 : Vertex) [(390 : Vertex), (407 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 88 = true ∨ valuation q 101 = true ∨ valuation q 113 = true := by
  rw [value88, value90, value101, value113, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(389 : Vertex), (407 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (390 : Vertex) [(389 : Vertex), (407 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 88 = true ∨ valuation q 89 = true ∨ valuation q 113 = true := by
  rw [value88, value89, value90, value113, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(389 : Vertex), (390 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (407 : Vertex) [(389 : Vertex), (390 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 88 = true ∨ valuation q 89 = true ∨ valuation q 101 = true := by
  rw [value88, value89, value90, value101, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(389 : Vertex), (390 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (455 : Vertex) [(389 : Vertex), (390 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value91, value92, value93, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(393 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (384 : Vertex) [(393 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 85 = true ∨ valuation q 93 = true := by
  rw [value85, value91, value93, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (393 : Vertex) [(384 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 85 = true ∨ valuation q 92 = true := by
  rw [value85, value91, value92, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (394 : Vertex) [(384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 91 = false := by
  rw [value18, value54, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (265 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 94 = false := by
  rw [value18, value54, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (265 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 95 = false := by
  rw [value18, value54, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (265 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 102 = false := by
  rw [value18, value54, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (265 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 54 = false ∨ valuation q 114 = false := by
  rw [value18, value54, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (265 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value18, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 91 = false ∨ valuation q 95 = false := by
  rw [value18, value91, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 18 = false ∨ valuation q 91 = false ∨ valuation q 102 = false := by
  rw [value18, value91, value92, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E052.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112052
