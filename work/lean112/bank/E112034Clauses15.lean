import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 87 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value87, value96, value97, value99, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(417 : Vertex), (432 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (497 : Vertex) [(417 : Vertex), (432 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 88 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value88, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (418 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value96, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (432 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 101 = true := by
  rw [value96, value98, value99, value101, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(432 : Vertex), (435 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (418 : Vertex) [(432 : Vertex), (435 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 99 = true ∨ valuation q 101 = true := by
  rw [value88, value98, value99, value101, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(418 : Vertex), (435 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (432 : Vertex) [(418 : Vertex), (435 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 96 = true ∨ valuation q 101 = true := by
  rw [value88, value96, value98, value101, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(418 : Vertex), (432 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (435 : Vertex) [(418 : Vertex), (432 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value88, value96, value98, value99, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(418 : Vertex), (432 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (442 : Vertex) [(418 : Vertex), (432 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value89, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 120 = false := by
  rw [value89, value97, value99, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 120 = false := by
  rw [value89, value98, value99, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (419 : Vertex) (434 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 120 = false := by
  rw [value97, value98, value99, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (434 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 120 = true := by
  rw [value97, value98, value99, value120, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(433 : Vertex), (434 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (419 : Vertex) [(433 : Vertex), (434 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 120 = true := by
  rw [value89, value98, value99, value120, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(419 : Vertex), (434 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (433 : Vertex) [(419 : Vertex), (434 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 96 = true ∨ valuation q 102 = true := by
  rw [value96, value100, value102, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(432 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (420 : Vertex) [(432 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 90 = true ∨ valuation q 102 = true := by
  rw [value90, value100, value102, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(420 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (432 : Vertex) [(420 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 90 = true ∨ valuation q 96 = true := by
  rw [value90, value96, value100, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(420 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (444 : Vertex) [(420 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 29 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value29, value93, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 29 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value29, value93, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 29 = false ∨ valuation q 93 = false ∨ valuation q 126 = false := by
  rw [value29, value93, value101, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 29 = false ∨ valuation q 98 = false ∨ valuation q 104 = false := by
  rw [value29, value98, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (434 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 29 = false ∨ valuation q 98 = false ∨ valuation q 126 = false := by
  rw [value29, value98, value101, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (434 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 29 = false ∨ valuation q 104 = false ∨ valuation q 126 = false := by
  rw [value29, value101, value104, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 104 = false := by
  rw [value93, value98, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (434 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 126 = false := by
  rw [value93, value98, value101, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (434 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 126 = false := by
  rw [value93, value101, value104, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 98 = false ∨ valuation q 104 = false ∨ valuation q 126 = false := by
  rw [value98, value101, value104, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 93 = true ∨ valuation q 98 = true ∨ valuation q 104 = true ∨ valuation q 126 = true := by
  rw [value93, value98, value101, value104, value126, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(426 : Vertex), (434 : Vertex), (446 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (186 : Vertex) [(426 : Vertex), (434 : Vertex), (446 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 29 = true ∨ valuation q 98 = true ∨ valuation q 104 = true ∨ valuation q 126 = true := by
  rw [value29, value98, value101, value104, value126, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(186 : Vertex), (434 : Vertex), (446 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (426 : Vertex) [(186 : Vertex), (434 : Vertex), (446 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 29 = true ∨ valuation q 93 = true ∨ valuation q 98 = true ∨ valuation q 126 = true := by
  rw [value29, value93, value98, value101, value126, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(186 : Vertex), (426 : Vertex), (434 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (446 : Vertex) [(186 : Vertex), (426 : Vertex), (434 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value100, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (436 : Vertex) (445 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 103 = true ∨ valuation q 104 = true := by
  rw [value102, value103, value104, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(445 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (436 : Vertex) [(445 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 230 = true ∨ valuation q 100 = true ∨ valuation q 103 = true := by
  rw [value100, value102, value103, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(436 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (446 : Vertex) [(436 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E034.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112034
