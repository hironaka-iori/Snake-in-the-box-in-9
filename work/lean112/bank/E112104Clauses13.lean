import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 87 = false ∨ valuation q 103 = false := by
  rw [value70, value87, value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (429 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 87 = false ∨ valuation q 106 = false := by
  rw [value70, value87, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (429 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 87 = false ∨ valuation q 117 = false := by
  rw [value70, value87, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (429 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value70, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value70, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (492 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 87 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value87, value103, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (429 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 87 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value87, value103, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (429 : Vertex) (489 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value103, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (489 : Vertex) (492 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 70 = true ∨ valuation q 87 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 117 = true := by
  rw [value70, value87, value103, value106, value107, value117, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(365 : Vertex), (429 : Vertex), (489 : Vertex), (492 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (237 : Vertex) [(365 : Vertex), (429 : Vertex), (489 : Vertex), (492 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 100 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value100, value104, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (494 : Vertex) (486 : Vertex) (490 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 104 = true ∨ valuation q 106 = true := by
  rw [value104, value106, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(490 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (486 : Vertex) [(490 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 100 = true ∨ valuation q 106 = true := by
  rw [value100, value106, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(486 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (490 : Vertex) [(486 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 100 = true ∨ valuation q 104 = true := by
  rw [value100, value104, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (494 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(486 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (494 : Vertex) (492 : Vertex) [(486 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 113 = true ∨ valuation q 116 = true := by
  rw [value109, value113, value116, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(503 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (483 : Vertex) [(503 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 98 = true ∨ valuation q 116 = true := by
  rw [value98, value109, value116, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(483 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (503 : Vertex) [(483 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 98 = true ∨ valuation q 113 = true := by
  rw [value98, value109, value113, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(483 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (507 : Vertex) [(483 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 110 = true := by
  rw [value110, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (500 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 41 = false ∨ valuation q 99 = false ∨ valuation q 111 = false := by
  rw [value41, value99, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (484 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 41 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value41, value99, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (484 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 41 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value41, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (501 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 113 = true ∨ valuation q 117 = true := by
  rw [value111, value113, value117, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(503 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (500 : Vertex) [(503 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 110 = true ∨ valuation q 117 = true := by
  rw [value110, value111, value117, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(500 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (503 : Vertex) [(500 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 110 = true ∨ valuation q 113 = true := by
  rw [value110, value111, value113, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (501 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(500 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (501 : Vertex) (509 : Vertex) [(500 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 230 = true ∨ valuation q 91 = true ∨ valuation q 100 = true ∨ valuation q 110 = true ∨ valuation q 113 = true := by
  rw [value91, value100, value110, value112, value113, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (374 : Vertex) → w ∈ [(438 : Vertex), (486 : Vertex), (500 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (374 : Vertex) [(438 : Vertex), (486 : Vertex), (500 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 101 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value101, value109, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (499 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 101 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value101, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 101 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value101, value109, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (499 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 101 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value101, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (501 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 101 = false ∨ valuation q 111 = false ∨ valuation q 118 = false := by
  rw [value101, value111, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (501 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 101 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value101, value112, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (487 : Vertex) (502 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value109, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (499 : Vertex) (501 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 118 = false := by
  rw [value109, value111, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (499 : Vertex) (501 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E104.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112104
