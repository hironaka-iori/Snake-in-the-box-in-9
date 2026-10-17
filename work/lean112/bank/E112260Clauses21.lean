import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 96 = true ∨ valuation q 98 = true := by
  rw [value96, value98, value99, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(359 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (495 : Vertex) [(359 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 101 = true := by
  rw [value91, value94, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ∈ [(341 : Vertex), (357 : Vertex), (375 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (373 : Vertex) [(341 : Vertex), (357 : Vertex), (375 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 101 = false := by
  rw [value91, value94, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (341 : Vertex) (357 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 94 = true ∨ valuation q 101 = true := by
  rw [value94, value100, value101, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(357 : Vertex), (375 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (341 : Vertex) [(357 : Vertex), (375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 91 = true ∨ valuation q 101 = true := by
  rw [value91, value100, value101, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(341 : Vertex), (375 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (357 : Vertex) [(341 : Vertex), (375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 91 = true ∨ valuation q 94 = true := by
  rw [value91, value94, value100, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(341 : Vertex), (357 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (375 : Vertex) [(341 : Vertex), (357 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 127 = false := by
  rw [value96, value100, value101, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (375 : Vertex) (359 : Vertex) (373 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 228 = true ∨ valuation q 96 = true ∨ valuation q 127 = true := by
  rw [value96, value101, value127, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(359 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(359 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 228 = true ∨ valuation q 96 = true ∨ valuation q 100 = true := by
  rw [value96, value100, value101, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (503 : Vertex) → w ∈ [(359 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (503 : Vertex) [(359 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 36 = false ∨ valuation q 103 = false ∨ valuation q 108 = false := by
  rw [value36, value102, value103, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (449 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 36 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value36, value102, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (452 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value102, value103, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (449 : Vertex) (452 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 229 = true ∨ valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 108 = true := by
  rw [value102, value103, value105, value108, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(449 : Vertex), (452 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (192 : Vertex) [(449 : Vertex), (452 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 37 = false ∨ valuation q 78 = false ∨ valuation q 102 = false := by
  rw [value37, value78, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (321 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 37 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value37, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (193 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 78 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value78, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (448 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 78 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value78, value103, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (321 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value103, value104, value106, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 78 = true ∨ valuation q 102 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 109 = true := by
  rw [value78, value102, value103, value104, value106, value109, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(321 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (193 : Vertex) [(321 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 37 = true ∨ valuation q 102 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 109 = true := by
  rw [value37, value102, value103, value104, value106, value109, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(193 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (321 : Vertex) [(193 : Vertex), (448 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 37 = true ∨ valuation q 78 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 109 = true := by
  rw [value37, value78, value103, value104, value106, value109, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (448 : Vertex) [(193 : Vertex), (321 : Vertex), (451 : Vertex), (453 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 79 = false ∨ valuation q 103 = false ∨ valuation q 110 = false := by
  rw [value79, value103, value104, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (449 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 79 = false ∨ valuation q 103 = false ∨ valuation q 113 = false := by
  rw [value79, value103, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (449 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 79 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value79, value103, value104, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (449 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 79 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value79, value104, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 79 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value79, value104, value110, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (459 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 79 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value79, value104, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (323 : Vertex) (467 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value103, value104, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value103, value104, value110, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (459 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value103, value104, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (449 : Vertex) (467 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value104, value110, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (459 : Vertex) (467 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 39 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value39, value105, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (196 : Vertex) (468 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E260.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112260
