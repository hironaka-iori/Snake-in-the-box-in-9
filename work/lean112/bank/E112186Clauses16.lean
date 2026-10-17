import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 90 = true ∨ valuation q 103 = true ∨ valuation q 104 = true := by
  rw [value90, value102, value103, value104, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(396 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (408 : Vertex) [(396 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 90 = true ∨ valuation q 99 = true ∨ valuation q 104 = true := by
  rw [value90, value99, value102, value104, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(396 : Vertex), (408 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (413 : Vertex) [(396 : Vertex), (408 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 90 = true ∨ valuation q 99 = true ∨ valuation q 103 = true := by
  rw [value90, value99, value102, value103, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(396 : Vertex), (408 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(396 : Vertex), (408 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value91, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (409 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 123 = false := by
  rw [value91, value100, value103, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (409 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 91 = false ∨ valuation q 102 = false ∨ valuation q 123 = false := by
  rw [value91, value102, value103, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (412 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 100 = false ∨ valuation q 102 = false ∨ valuation q 123 = false := by
  rw [value100, value102, value103, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (409 : Vertex) (412 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 123 = true := by
  rw [value91, value100, value103, value123, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(397 : Vertex), (409 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (412 : Vertex) [(397 : Vertex), (409 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 92 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value92, value98, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 92 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value92, value98, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 92 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value92, value101, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value98, value101, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 92 = true ∨ valuation q 98 = true ∨ valuation q 102 = true := by
  rw [value92, value98, value102, value104, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(398 : Vertex), (406 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (410 : Vertex) [(398 : Vertex), (406 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 30 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value30, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (450 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 30 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value30, value105, value106, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (450 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 30 = false ∨ valuation q 106 = false ∨ valuation q 116 = false := by
  rw [value30, value105, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 30 = false ∨ valuation q 111 = false ∨ valuation q 116 = false := by
  rw [value30, value105, value111, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (456 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 82 = false ∨ valuation q 106 = false ∨ valuation q 116 = false := by
  rw [value82, value105, value106, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (384 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 111 = false ∨ valuation q 116 = false := by
  rw [value105, value106, value111, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (450 : Vertex) (456 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 84 = false ∨ valuation q 105 = false := by
  rw [value66, value84, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 84 = false ∨ valuation q 107 = false := by
  rw [value66, value84, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 84 = false ∨ valuation q 109 = false := by
  rw [value66, value84, value106, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 84 = false ∨ valuation q 113 = false := by
  rw [value66, value84, value106, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value66, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value66, value105, value106, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (448 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value66, value105, value106, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (448 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value66, value106, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value66, value106, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 66 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value66, value106, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (454 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 84 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value84, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 84 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value84, value105, value106, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 84 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value84, value105, value106, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (448 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E186.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112186
