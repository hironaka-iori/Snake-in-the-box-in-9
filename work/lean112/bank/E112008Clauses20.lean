import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 105 = true := by
  rw [value99, value100, value101, value105, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(433 : Vertex), (434 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (419 : Vertex) [(433 : Vertex), (434 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 89 = true ∨ valuation q 100 = true ∨ valuation q 105 = true := by
  rw [value89, value100, value101, value105, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(419 : Vertex), (434 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (433 : Vertex) [(419 : Vertex), (434 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 89 = true ∨ valuation q 99 = true ∨ valuation q 105 = true := by
  rw [value89, value99, value101, value105, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(419 : Vertex), (433 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (434 : Vertex) [(419 : Vertex), (433 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 79 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value79, value98, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (308 : Vertex) (432 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 79 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value79, value102, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (308 : Vertex) (444 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 98 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value98, value102, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (432 : Vertex) (444 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 98 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value98, value102, value106, value118, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(432 : Vertex), (444 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (308 : Vertex) [(432 : Vertex), (444 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 226 = true ∨ valuation q 79 = true ∨ valuation q 98 = true ∨ valuation q 118 = true := by
  rw [value79, value98, value102, value118, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(308 : Vertex), (432 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (444 : Vertex) [(308 : Vertex), (432 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value47, value98, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (432 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 47 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value47, value103, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (184 : Vertex) (442 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 92 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value92, value98, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (432 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 92 = true ∨ valuation q 98 = true ∨ valuation q 104 = true ∨ valuation q 106 = true := by
  rw [value92, value98, value103, value104, value106, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(424 : Vertex), (432 : Vertex), (442 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (184 : Vertex) [(424 : Vertex), (432 : Vertex), (442 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 47 = true ∨ valuation q 98 = true ∨ valuation q 104 = true ∨ valuation q 106 = true := by
  rw [value47, value98, value103, value104, value106, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(184 : Vertex), (432 : Vertex), (442 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(184 : Vertex), (432 : Vertex), (442 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 47 = true ∨ valuation q 92 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value47, value92, value98, value103, value106, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (432 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(184 : Vertex), (424 : Vertex), (432 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 227 = true ∨ valuation q 47 = true ∨ valuation q 92 = true ∨ valuation q 98 = true ∨ valuation q 104 = true := by
  rw [value47, value92, value98, value103, value104, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex), (432 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (444 : Vertex) [(184 : Vertex), (424 : Vertex), (432 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value83, value100, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (434 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 105 = false := by
  rw [value83, value100, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (434 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value83, value100, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (434 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value83, value100, value104, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (434 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value83, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value83, value103, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 103 = false ∨ valuation q 122 = false := by
  rw [value83, value103, value104, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value83, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 105 = false ∨ valuation q 122 = false := by
  rw [value83, value104, value105, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 83 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value83, value104, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (314 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value100, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 107 = false := by
  rw [value100, value103, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 122 = false := by
  rw [value100, value103, value104, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 100 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value100, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 100 = false ∨ valuation q 105 = false ∨ valuation q 122 = false := by
  rw [value100, value104, value105, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 100 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value100, value104, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value103, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E008.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112008
