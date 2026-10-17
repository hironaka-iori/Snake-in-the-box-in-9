import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value27, value101, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value62, value90, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 90 = false ∨ valuation q 100 = false := by
  rw [value62, value90, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 90 = false ∨ valuation q 107 = false := by
  rw [value62, value90, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 90 = false ∨ valuation q 122 = false := by
  rw [value62, value90, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value62, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value62, value99, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (405 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 99 = false ∨ valuation q 122 = false := by
  rw [value62, value99, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (405 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value62, value100, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value62, value100, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 62 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value62, value101, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 90 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value90, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 90 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value90, value99, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 90 = false ∨ valuation q 99 = false ∨ valuation q 122 = false := by
  rw [value90, value99, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (405 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 90 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value90, value100, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 90 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value90, value100, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 90 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value90, value101, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value99, value100, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (405 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value99, value100, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (405 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value99, value101, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (405 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 100 = false ∨ valuation q 107 = false ∨ valuation q 122 = false := by
  rw [value100, value101, value107, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (406 : Vertex) (415 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 228 = true ∨ valuation q 62 = true ∨ valuation q 90 = true ∨ valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 107 = true ∨ valuation q 122 = true := by
  rw [value62, value90, value99, value100, value101, value107, value122, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(279 : Vertex), (391 : Vertex), (405 : Vertex), (406 : Vertex), (415 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (151 : Vertex) [(279 : Vertex), (391 : Vertex), (405 : Vertex), (406 : Vertex), (415 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 104 = false := by
  rw [value92, value97, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 105 = false := by
  rw [value92, value97, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (401 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 92 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value92, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 97 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value97, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (401 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 229 = true ∨ valuation q 97 = true ∨ valuation q 104 = true ∨ valuation q 105 = true := by
  rw [value97, value102, value104, value105, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (393 : Vertex) [(401 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 229 = true ∨ valuation q 92 = true ∨ valuation q 104 = true ∨ valuation q 105 = true := by
  rw [value92, value102, value104, value105, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(393 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(393 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 229 = true ∨ valuation q 92 = true ∨ valuation q 97 = true ∨ valuation q 105 = true := by
  rw [value92, value97, value102, value105, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(393 : Vertex), (401 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 229 = true ∨ valuation q 92 = true ∨ valuation q 97 = true ∨ valuation q 104 = true := by
  rw [value92, value97, value102, value104, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (413 : Vertex) [(393 : Vertex), (401 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 93 = true ∨ valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 124 = true := by
  rw [value93, value103, value104, value106, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ∈ [(394 : Vertex), (411 : Vertex), (414 : Vertex), (474 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (410 : Vertex) [(394 : Vertex), (411 : Vertex), (414 : Vertex), (474 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value93, value103, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (394 : Vertex) (411 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E052.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112052
