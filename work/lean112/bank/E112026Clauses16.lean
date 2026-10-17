import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 98 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value95, value98, value102, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 61 = true ∨ valuation q 97 = true ∨ valuation q 116 = true := by
  rw [value61, value96, value97, value116, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(308 : Vertex), (437 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (420 : Vertex) [(308 : Vertex), (437 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 61 = true ∨ valuation q 84 = true ∨ valuation q 116 = true := by
  rw [value61, value84, value96, value116, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(308 : Vertex), (420 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (437 : Vertex) [(308 : Vertex), (420 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 61 = true ∨ valuation q 84 = true ∨ valuation q 97 = true := by
  rw [value61, value84, value96, value97, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(308 : Vertex), (420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (500 : Vertex) [(308 : Vertex), (420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value85, value94, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (433 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value85, value94, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 85 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value85, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value94, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (433 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 85 = false ∨ valuation q 96 = false := by
  rw [value85, value96, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 218 = true ∨ valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 98 = true := by
  rw [value94, value96, value97, value98, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(433 : Vertex), (436 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (421 : Vertex) [(433 : Vertex), (436 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 218 = true ∨ valuation q 85 = true ∨ valuation q 94 = true ∨ valuation q 98 = true := by
  rw [value85, value94, value97, value98, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(421 : Vertex), (433 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (436 : Vertex) [(421 : Vertex), (433 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 103 = true := by
  rw [value87, value95, value97, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ∈ [(423 : Vertex), (435 : Vertex), (437 : Vertex), (447 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (439 : Vertex) [(423 : Vertex), (435 : Vertex), (437 : Vertex), (447 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value87, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (423 : Vertex) (435 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 103 = false := by
  rw [value87, value97, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (439 : Vertex) (423 : Vertex) (437 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 103 = true := by
  rw [value95, value97, value98, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(435 : Vertex), (437 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (423 : Vertex) [(435 : Vertex), (437 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 87 = true ∨ valuation q 97 = true ∨ valuation q 103 = true := by
  rw [value87, value97, value98, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(423 : Vertex), (437 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (435 : Vertex) [(423 : Vertex), (437 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 103 = true := by
  rw [value87, value95, value98, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (437 : Vertex) [(423 : Vertex), (435 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 97 = true := by
  rw [value87, value95, value97, value98, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (447 : Vertex) [(423 : Vertex), (435 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value27, value88, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (424 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value27, value88, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (424 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 88 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value88, value99, value100, value101, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(424 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (184 : Vertex) [(424 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 27 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value27, value99, value100, value101, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(184 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(184 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 27 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value27, value88, value99, value101, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (441 : Vertex) [(184 : Vertex), (424 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 27 = true ∨ valuation q 88 = true ∨ valuation q 100 = true := by
  rw [value27, value88, value99, value100, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(184 : Vertex), (424 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 94 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value94, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (433 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 94 = true ∨ valuation q 102 = true := by
  rw [value94, value100, value102, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(433 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (440 : Vertex) [(433 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 94 = true ∨ valuation q 99 = true := by
  rw [value94, value99, value100, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(433 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (443 : Vertex) [(433 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value89, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 118 = false := by
  rw [value89, value99, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 102 = false ∨ valuation q 118 = false := by
  rw [value89, value101, value102, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 118 = false := by
  rw [value99, value101, value102, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 102 = false ∨ valuation q 118 = false := by
  rw [value102, value118, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (442 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E026.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112026
