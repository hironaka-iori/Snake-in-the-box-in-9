import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value94, value95, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value94, value95, value102, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 98 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value95, value98, value102, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 116 = true := by
  rw [value96, value97, value116, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(437 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (420 : Vertex) [(437 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 84 = true ∨ valuation q 116 = true := by
  rw [value84, value96, value116, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(420 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (437 : Vertex) [(420 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 84 = true ∨ valuation q 97 = true := by
  rw [value84, value96, value97, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (500 : Vertex) [(420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value85, value94, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (433 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value85, value94, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 85 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value85, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value94, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (433 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 218 = true ∨ valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 98 = true := by
  rw [value94, value96, value97, value98, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(433 : Vertex), (436 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (421 : Vertex) [(433 : Vertex), (436 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 218 = true ∨ valuation q 85 = true ∨ valuation q 94 = true ∨ valuation q 98 = true := by
  rw [value85, value94, value97, value98, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(421 : Vertex), (433 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (436 : Vertex) [(421 : Vertex), (433 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 103 = true := by
  rw [value95, value97, value98, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(435 : Vertex), (437 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (423 : Vertex) [(435 : Vertex), (437 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 87 = true ∨ valuation q 97 = true ∨ valuation q 103 = true := by
  rw [value87, value97, value98, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(423 : Vertex), (437 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (435 : Vertex) [(423 : Vertex), (437 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 103 = true := by
  rw [value87, value95, value98, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (437 : Vertex) [(423 : Vertex), (435 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 97 = true := by
  rw [value87, value95, value97, value98, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(423 : Vertex), (435 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (447 : Vertex) [(423 : Vertex), (435 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value27, value88, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (424 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value27, value88, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (424 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 88 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value88, value99, value100, value101, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(424 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (184 : Vertex) [(424 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 27 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value27, value99, value100, value101, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(184 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(184 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 27 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value27, value88, value99, value101, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (441 : Vertex) [(184 : Vertex), (424 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 220 = true ∨ valuation q 27 = true ∨ valuation q 88 = true ∨ valuation q 100 = true := by
  rw [value27, value88, value99, value100, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(184 : Vertex), (424 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 94 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value94, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (441 : Vertex) (433 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value94, value99, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (441 : Vertex) (433 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value99, value102, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (441 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 221 = true ∨ valuation q 94 = true ∨ valuation q 102 = true := by
  rw [value94, value100, value102, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(433 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (440 : Vertex) [(433 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value89, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 118 = false := by
  rw [value89, value99, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 102 = false ∨ valuation q 118 = false := by
  rw [value89, value101, value102, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 118 = false := by
  rw [value99, value101, value102, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 222 = true ∨ valuation q 89 = true ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value89, value99, value101, value102, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(426 : Vertex), (440 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (506 : Vertex) [(426 : Vertex), (440 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 90 = false ∨ valuation q 95 = false ∨ valuation q 100 = false := by
  rw [value90, value95, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E024.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112024
