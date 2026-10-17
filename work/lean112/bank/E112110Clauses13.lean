import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 111 = true := by
  rw [value97, value98, value99, value101, value103, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ∈ [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (451 : Vertex) [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value97, value99, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (455 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 97 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value97, value99, value103, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 111 = true := by
  rw [value97, value99, value101, value103, value111, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(449 : Vertex), (455 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 103 = true ∨ valuation q 111 = true := by
  rw [value97, value98, value99, value103, value111, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (455 : Vertex) [(449 : Vertex), (450 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 111 = true := by
  rw [value97, value98, value99, value101, value111, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(449 : Vertex), (450 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 103 = true := by
  rw [value97, value98, value99, value101, value103, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (467 : Vertex) [(449 : Vertex), (450 : Vertex), (455 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value80, value97, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 80 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value80, value97, value100, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 97 = true ∨ valuation q 101 = true ∨ valuation q 105 = true := by
  rw [value97, value100, value101, value105, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (389 : Vertex) [(449 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 80 = true ∨ valuation q 101 = true ∨ valuation q 105 = true := by
  rw [value80, value100, value101, value105, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(389 : Vertex), (455 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (449 : Vertex) [(389 : Vertex), (455 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 80 = true ∨ valuation q 97 = true ∨ valuation q 101 = true := by
  rw [value80, value97, value100, value101, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(389 : Vertex), (449 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (461 : Vertex) [(389 : Vertex), (449 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 107 = true := by
  rw [value37, value99, value100, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ∈ [(199 : Vertex), (451 : Vertex), (453 : Vertex), (463 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (455 : Vertex) [(199 : Vertex), (451 : Vertex), (453 : Vertex), (463 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value37, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value37, value99, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 37 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value37, value100, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value99, value100, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 107 = true := by
  rw [value99, value100, value101, value107, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(451 : Vertex), (453 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (199 : Vertex) [(451 : Vertex), (453 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 37 = true ∨ valuation q 100 = true ∨ valuation q 107 = true := by
  rw [value37, value100, value101, value107, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(199 : Vertex), (453 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (451 : Vertex) [(199 : Vertex), (453 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 38 = false ∨ valuation q 63 = false ∨ valuation q 82 = false := by
  rw [value38, value63, value82, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (328 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 38 = false ∨ valuation q 82 = false ∨ valuation q 96 = false := by
  rw [value38, value82, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 38 = false ∨ valuation q 82 = false ∨ valuation q 104 = false := by
  rw [value38, value82, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (392 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 38 = false ∨ valuation q 82 = false ∨ valuation q 113 = false := by
  rw [value38, value82, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (392 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 38 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value38, value102, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (200 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 82 = false ∨ valuation q 96 = false := by
  rw [value63, value82, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (392 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 82 = false ∨ valuation q 104 = false := by
  rw [value63, value82, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (392 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 82 = false ∨ valuation q 113 = false := by
  rw [value63, value82, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (392 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 96 = false ∨ valuation q 104 = false := by
  rw [value63, value96, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 96 = false ∨ valuation q 113 = false := by
  rw [value63, value96, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (448 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 63 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value63, value102, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (328 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 82 = false ∨ valuation q 96 = false ∨ valuation q 104 = false := by
  rw [value82, value96, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (392 : Vertex) (448 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 82 = false ∨ valuation q 96 = false ∨ valuation q 113 = false := by
  rw [value82, value96, value102, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (392 : Vertex) (448 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E110.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112110
