import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 94 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value94, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (400 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 94 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value94, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (400 : Vertex) (409 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 94 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value94, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (400 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value99, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 27 = false ∨ valuation q 61 = false ∨ valuation q 88 = false := by
  rw [value27, value61, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (153 : Vertex) (281 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 27 = false ∨ valuation q 61 = false ∨ valuation q 120 = false := by
  rw [value27, value61, value100, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (153 : Vertex) (281 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value27, value88, value95, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (153 : Vertex) (393 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 103 = false := by
  rw [value27, value88, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (153 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 27 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value27, value95, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (153 : Vertex) (401 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 27 = false ∨ valuation q 95 = false ∨ valuation q 120 = false := by
  rw [value27, value95, value100, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (153 : Vertex) (401 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 61 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value61, value88, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (281 : Vertex) (393 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 61 = false ∨ valuation q 95 = false ∨ valuation q 103 = false := by
  rw [value61, value95, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (281 : Vertex) (401 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 61 = false ∨ valuation q 95 = false ∨ valuation q 120 = false := by
  rw [value61, value95, value100, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (281 : Vertex) (401 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 61 = false ∨ valuation q 99 = false ∨ valuation q 120 = false := by
  rw [value61, value99, value100, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (281 : Vertex) (408 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 61 = false ∨ valuation q 103 = false ∨ valuation q 120 = false := by
  rw [value61, value100, value103, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (281 : Vertex) (413 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 95 = false ∨ valuation q 99 = false := by
  rw [value88, value95, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 95 = false ∨ valuation q 120 = false := by
  rw [value88, value95, value100, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 88 = false ∨ valuation q 103 = false ∨ valuation q 120 = false := by
  rw [value88, value100, value103, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (413 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 95 = false ∨ valuation q 99 = false ∨ valuation q 120 = false := by
  rw [value95, value99, value100, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (401 : Vertex) (408 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 95 = false ∨ valuation q 103 = false ∨ valuation q 120 = false := by
  rw [value95, value100, value103, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (401 : Vertex) (413 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 96 = false ∨ valuation q 99 = false := by
  rw [value89, value96, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (394 : Vertex) (402 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 96 = false ∨ valuation q 104 = false := by
  rw [value89, value96, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (394 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 104 = false := by
  rw [value89, value99, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (394 : Vertex) (408 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 104 = false := by
  rw [value96, value99, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (402 : Vertex) (408 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 121 = false := by
  rw [value96, value99, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (402 : Vertex) (408 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 96 = false ∨ valuation q 104 = false ∨ valuation q 121 = false := by
  rw [value96, value101, value104, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (402 : Vertex) (414 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 104 = false ∨ valuation q 121 = false := by
  rw [value99, value101, value104, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (408 : Vertex) (414 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 89 = true ∨ valuation q 99 = true ∨ valuation q 104 = true ∨ valuation q 121 = true := by
  rw [value89, value99, value101, value104, value121, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(394 : Vertex), (408 : Vertex), (414 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (402 : Vertex) [(394 : Vertex), (408 : Vertex), (414 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 89 = true ∨ valuation q 96 = true ∨ valuation q 104 = true ∨ valuation q 121 = true := by
  rw [value89, value96, value101, value104, value121, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(394 : Vertex), (402 : Vertex), (414 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (408 : Vertex) [(394 : Vertex), (402 : Vertex), (414 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 89 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 121 = true := by
  rw [value89, value96, value99, value101, value121, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(394 : Vertex), (402 : Vertex), (408 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (414 : Vertex) [(394 : Vertex), (402 : Vertex), (408 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 89 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 104 = true := by
  rw [value89, value96, value99, value101, value104, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(394 : Vertex), (402 : Vertex), (408 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (474 : Vertex) [(394 : Vertex), (402 : Vertex), (408 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 99 = true ∨ valuation q 103 = true ∨ valuation q 104 = true := by
  rw [value99, value102, value103, value104, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(408 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (396 : Vertex) [(408 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E186.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112186
