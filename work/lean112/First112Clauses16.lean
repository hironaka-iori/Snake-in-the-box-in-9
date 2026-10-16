import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 94 = false ∨ valuation q 100 = false := by
  rw [value89, value94, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value89, value94, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value89, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value89, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (442 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 94 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value94, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 94 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 102 = true := by
  rw [value94, value99, value100, value101, value102, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(435 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (427 : Vertex) [(435 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 89 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 102 = true := by
  rw [value89, value99, value100, value101, value102, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(427 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (435 : Vertex) [(427 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 89 = true ∨ valuation q 94 = true ∨ valuation q 100 = true ∨ valuation q 102 = true := by
  rw [value89, value94, value100, value101, value102, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (441 : Vertex) [(427 : Vertex), (435 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 89 = true ∨ valuation q 94 = true ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value89, value94, value99, value101, value102, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (442 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 89 = true ∨ valuation q 94 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value89, value94, value99, value100, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (447 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value92, value97, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 122 = false := by
  rw [value92, value97, value102, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (439 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 92 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value92, value101, value102, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (443 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value97, value101, value102, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (439 : Vertex) (443 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 224 = true ∨ valuation q 92 = true ∨ valuation q 101 = true ∨ valuation q 122 = true := by
  rw [value92, value101, value102, value122, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(431 : Vertex), (443 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (439 : Vertex) [(431 : Vertex), (443 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 104 = false := by
  rw [value72, value80, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (416 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 105 = false := by
  rw [value72, value80, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (416 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 109 = false := by
  rw [value72, value80, value103, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (416 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 80 = false ∨ valuation q 113 = false := by
  rw [value72, value80, value103, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (416 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value72, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (481 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 104 = false ∨ valuation q 109 = false := by
  rw [value72, value103, value104, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value72, value103, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (481 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value72, value103, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value72, value103, value105, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (482 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 72 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value72, value103, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 80 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value80, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 80 = false ∨ valuation q 104 = false ∨ valuation q 109 = false := by
  rw [value80, value103, value104, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 80 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value80, value103, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 80 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value80, value103, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 80 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value80, value103, value105, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (482 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 80 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value80, value103, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value103, value104, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (481 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.First112
